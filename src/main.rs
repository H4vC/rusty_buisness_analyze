use std::{fmt, fs};
use std::any::Any;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::io::Read;
use std::path::Path;
use std::ptr::{copy, null_mut};
use anyhow::{anyhow, Result};
use goblin::{Object, pe};
use iced_x86::{Code, code_asm::CodeAssembler, Decoder, DecoderOptions, FastFormatter, FlowControl, Formatter, Instruction, InstructionInfoFactory, MasmFormatter, OpAccess, Register, RflagsBits};
use itertools::Itertools;
use petgraph::dot::Dot;
use petgraph::Graph;
use petgraph::graph::NodeIndex;
use rand::{prelude::*, random, Rng};
use windows_sys::Win32::System::Memory::{MEM_COMMIT, PAGE_EXECUTE_READWRITE, PAGE_READWRITE};

use crate::tools::{BasicBlockVecExt, SplitThisMut};
use crate::tools::InstructionExt;

mod tools;
struct AnalysisTarget {
    architecture: u32,
    func_start: usize,
    image_base: usize,
    data: Vec<u8>,
}
#[derive(Debug, Default, Clone)]
#[derive(PartialEq, Eq)]
struct LiveState {
    live_flags: u32,
    live_regs: HashSet<Register>,
}
impl fmt::Display for LiveState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut flags = String::new();
        let mut regs = String::new();

        if self.live_flags != RflagsBits::NONE {
            flags = LiveState::flagmask_str(self.live_flags).to_string();
        }
        if !self.live_regs.is_empty() {
            if self.live_regs.len() > 1 {
                regs = self.live_regs.iter().sorted().fold(String::new(), |acc, &arg| acc + &format!("{arg:?} ")).trim().to_string();
            } else {
                regs = format!("{:?}", self.live_regs.iter().next().unwrap());
            }
        }

        write!(f, "({flags})({regs})")
    }
}

static FLAG_NAMES: &[(u32, &str)] = &[
    (RflagsBits::OF, "OF"),
    (RflagsBits::SF, "SF"),
    (RflagsBits::ZF, "ZF"),
    (RflagsBits::AF, "AF"),
    (RflagsBits::CF, "CF"),
    (RflagsBits::PF, "PF"),
    (RflagsBits::DF, "DF"),
    (RflagsBits::IF, "IF"),
    (RflagsBits::AC, "AC"),
    (RflagsBits::UIF, "UIF"),
    (RflagsBits::C0, "C0"),
    (RflagsBits::C1, "C1"),
    (RflagsBits::C2, "C2"),
    (RflagsBits::C3, "C3"),
];

impl LiveState {
    fn flagmask_str(flagmask: u32) -> String {
        let mut sb = String::new();
        for (flag, name) in FLAG_NAMES {
            if (flagmask & flag) != 0 {
                if !sb.is_empty() {
                    sb.push(' ');
                }
                sb.push_str(name);
            }
        }
        sb
    }
}
#[derive(Debug)]
struct BasicBlock {
    label: u64,
    instructions: Vec<Instruction>,
    pre_blocks: Vec<u64>,
    post_blocks: Vec<u64>,
    liveness_map: HashMap<u64, LiveState>,
    live_in: LiveState,
    live_out: LiveState,
}
struct CodeAnalysis {
    instructions: Vec<Instruction>,
    blocks: Vec<BasicBlock>,
    c_flow_graph: Graph<String, String>,
}

impl AnalysisTarget {
    pub fn from_pe_with_export(path: &Path, export_name: &str) -> Result<Self> {
        let file_buff = fs::read(path)?;


        let Object::PE(pe) = Object::parse(&file_buff)? else { return Err(anyhow!("unknown PE format")) };

        let architecture = match pe.header.coff_header.machine {
            pe::header::COFF_MACHINE_X86 => 32,
            pe::header::COFF_MACHINE_X86_64 => 64,
            _ => {
                return Err(anyhow!(
                    "unknown PE (COFF) machine: {}",
                    pe.header.coff_header.machine
                ))
            }
        };

        let Some(func_export) = pe.exports.iter().find(|&e| e.name.unwrap_or("") == export_name) else {
            return Err(anyhow!("could not find export"));
        };

        let Some(exception_data) = &pe.exception_data else {
            return Err(anyhow!("Could not find exception data"))
        };

        let func_export_addr = func_export.rva;

        let Some(function_exception_data) = exception_data.find_function(u32::try_from(func_export_addr)?)? else {
            return Err(anyhow!("Could not find exception data"))
        };


        let func_start = function_exception_data.begin_address as usize;
        let func_end = function_exception_data.end_address as usize;
        let func_size = func_end - func_start;


        let mut function_buffer = vec![0u8; func_size];
        let Some(offset) = func_export.offset else {
            return Err(anyhow!("Found export did not contain file offset"));
        };
        (&file_buff[offset..]).read_exact(&mut function_buffer)?;


        Ok(AnalysisTarget {
            architecture,
            func_start,
            image_base: pe.image_base,
            data: function_buffer,
        })
    }


    fn disassemble(&self) -> Vec<Instruction> {
        let mut decoder = Decoder::with_ip(self.architecture, &self.data, self.func_start as u64 + self.image_base as u64, DecoderOptions::NONE);
        let instructions = decoder.iter().collect();
        instructions
    }

    pub fn analyze(&self) -> CodeAnalysis {
        let instructions = self.disassemble();

        let mut code_analysis = CodeAnalysis { instructions: instructions.clone(), blocks: Vec::new(), c_flow_graph: Graph::new() };
        code_analysis.add_blocks().unwrap();
        code_analysis.make_graph();

        assert_eq!(code_analysis.instructions.len(), code_analysis.blocks.get_instruction_count());

        code_analysis
    }
}
impl CodeAnalysis {
    fn add_blocks(&mut self) -> Result<()> {
        if self.instructions.is_empty() { return Err(anyhow!("Instruction List empty")); }

        //Break Function into basic blocks
        let mut block_starts = HashSet::new();
        block_starts.insert(self.instructions.first().unwrap().ip());

        for inst in &self.instructions {
            if inst.flow_control() != FlowControl::Next {
                for addr in inst.get_possible_flows() {
                    block_starts.insert(addr);
                }
            }
        }

        for bs in &block_starts {
            let instructions: Vec<_> = self.instructions.iter().skip_while(|&instr| &instr.ip() != bs).take_while(|inst|
            (&inst.ip() == bs) || !block_starts.contains(&inst.ip())).copied().collect();

            let post_blocks = instructions.last().unwrap().get_possible_flows();

            self.blocks.push(BasicBlock { label: *bs, instructions, post_blocks, pre_blocks: Vec::new(), live_in: LiveState::default(), live_out: LiveState::default(), liveness_map: HashMap::new() });
        }
        self.blocks.sort();

        for i in 0..self.blocks.len() {
            let (bb, other_blocks) = self.blocks.split_this_mut(i);
            let pre_blocks = other_blocks.filter(|p| p.post_blocks.contains(&bb.label)).map(|bb| bb.label).collect();
            bb.pre_blocks = pre_blocks;
        }

        let mut block_queue = VecDeque::new();
        block_queue.extend(self.blocks.iter().filter(|b| b.instructions.iter().any(|i| i.flow_control() == FlowControl::Return)).map(|b| b.label)); //returning blocks
        while !block_queue.is_empty() {
            let label = block_queue.pop_front().unwrap();

            let block = self.blocks.get_with_label_as_mut(label).unwrap();
            let mut info_factory = InstructionInfoFactory::new();

            let mut l_current = block.live_out.clone();

            for inst in block.instructions.iter().rev() {
                let used_regs = info_factory.info(inst).used_registers();
                let mut regs_read = used_regs.iter().filter(|&r| matches!(r.access(), OpAccess::Read | OpAccess::CondRead | OpAccess::ReadWrite | OpAccess::ReadCondWrite)).map(|r| r.register().full_register()).filter(|r| !r.is_segment_register()).collect(); //Mark Reads as Full Regs
                let mut regs_wrote = used_regs.iter().filter(|&r| matches!(r.access(), OpAccess::Write | OpAccess::CondWrite | OpAccess::ReadWrite | OpAccess::ReadCondWrite)).map(iced_x86::UsedRegister::register).collect();

                match inst.flow_control() {
                    FlowControl::Return => {
                        regs_read = vec![Register::R12, Register::R13, Register::R14, Register::R15, Register::RDI, Register::RSI, Register::RBX, Register::RBP, Register::RSP, Register::RAX]; //Non volatile registers r-12->15 di si bx bp sp + RAX
                        regs_wrote = vec![];
                    }
                    FlowControl::Call | FlowControl::IndirectCall => {
                        regs_read = vec![Register::RCX, Register::RDX, Register::R8, Register::R9];
                        regs_wrote = vec![Register::RAX, Register::RCX, Register::RDX, Register::R8, Register::R9, Register::R10, Register::R11];
                    }
                    _ => {}
                }

                if inst.rflags_read() != RflagsBits::NONE {
                    l_current.live_flags |= inst.rflags_read();
                }
                if !regs_read.is_empty() {
                    l_current.live_regs.extend(regs_read.clone());
                }

                block.liveness_map.insert(inst.ip(), l_current.clone());

                if inst.rflags_modified() != RflagsBits::NONE {
                    l_current.live_flags &= !(inst.rflags_modified() & !inst.rflags_read());
                }
                if !regs_wrote.is_empty() {
                    let mut only_written: HashSet<Register> = HashSet::new();
                    only_written.extend(regs_wrote.iter().filter(|r| !regs_read.contains(r)));
                    l_current.live_regs = l_current.live_regs.clone().into_iter().filter(|r| !only_written.contains(r)).collect();
                }
            }

            if l_current != block.live_in {
                block.live_in = l_current.clone();
                for pred_label in &block.pre_blocks.clone() {
                    let p_block = self.blocks.get_with_label_as_mut(*pred_label).unwrap();
                    let mut extended_live_out = p_block.live_out.clone();

                    extended_live_out.live_flags |= l_current.live_flags;
                    extended_live_out.live_regs.extend(l_current.live_regs.clone());

                    p_block.live_out = extended_live_out;
                    block_queue.push_front(*pred_label);
                }
            }
        }
        Ok(())
    }
    fn make_graph(&mut self) {
        fn insert_node_into_graph(basic_block: &BasicBlock, visited: &HashMap<u64, NodeIndex>, c_flow_graph: &mut Graph<String, String>) -> NodeIndex {
            let mut output = String::new();
            let mut formatter = FastFormatter::new();
            let instructions = &basic_block.instructions;

            let pi = if visited.contains_key(&basic_block.label) {
                visited[&basic_block.label]
            } else {
                for i in instructions {
                    formatter.format(i, &mut output);
                    output.push('\n');
                }
                c_flow_graph.add_node(format!("{:#01x}\n{output}", basic_block.label))
            };
            output.clear();
            pi
        }

        let mut c_flow_graph = Graph::new();
        let mut visited = HashMap::new();
        for block in &self.blocks {
            let pi = insert_node_into_graph(block, &visited, &mut c_flow_graph);

            for post_label in &block.post_blocks {
                let inner_block = &self.blocks.get_with_label(*post_label).unwrap();
                let inner_block_ni = insert_node_into_graph(inner_block, &visited, &mut c_flow_graph);

                let branching = if block.instructions.last().unwrap().flow_control() == FlowControl::ConditionalBranch { //if conditional update edge descriptor
                    if block.instructions.last().unwrap().near_branch_target() == *post_label { "taken".to_string() } else { "not_taken".to_string() }
                } else {
                    String::new()
                };

                c_flow_graph.update_edge(pi, inner_block_ni, branching);

                visited.insert(*post_label, inner_block_ni);
            }
        }
        self.c_flow_graph = c_flow_graph;
    }
}

impl Ord for BasicBlock {
    fn cmp(&self, other: &Self) -> Ordering {
        self.label.cmp(&other.label)
    }
}

impl PartialEq<Self> for BasicBlock {
    fn eq(&self, other: &Self) -> bool {
        self.label == other.label
    }
}

impl Eq for BasicBlock {}

impl PartialOrd for BasicBlock {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for BasicBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut formatted_disassembly = String::new();
        let mut masm_formatter = MasmFormatter::new();
        let mut coll = String::new();

        coll.push_str(&format!("Block {:#01x}", self.label));
        coll.push('\n');
        coll.push_str(&format!("In :{}", self.live_in));
        coll.push('\n');
        coll.push_str(&format!("Out:{}", self.live_out));
        coll.push('\n');

        self.instructions.iter().for_each(|i| {
            formatted_disassembly.push_str(&format!("{:#01x} ", &i.ip()).to_string().to_string());
            masm_formatter.format(i, &mut formatted_disassembly);
            formatted_disassembly.push_str(&format!(" {}", self.liveness_map[&i.ip()]).to_string());
            formatted_disassembly.push('\n');
        });

        coll.push_str(&formatted_disassembly.to_string());


        match self.pre_blocks.len() {
            0 => {}
            1 => {
                coll.push_str(&format!("PreBlocks  {}: {}", self.pre_blocks.len(), &format!("{:#01x}", self.pre_blocks.first().unwrap())));
                coll.push('\n');
            }
            _ => {
                coll.push_str(&format!("PreBlocks  {}: {}", self.pre_blocks.len(), self.pre_blocks.iter().fold(String::new(), |acc, &arg| acc + &format!("{arg:#01x}, "))));
                coll.push('\n');
            }
        }

        match self.post_blocks.len() {
            0 => {}
            1 => {
                coll.push_str(&format!("PostBlocks {}: {}", self.post_blocks.len(), &format!("{:#01x}", self.post_blocks.first().unwrap())));
                coll.push('\n');
            }
            _ => {
                coll.push_str(&format!("PostBlocks {}: {}", self.post_blocks.len(), self.post_blocks.iter().fold(String::new(), |acc, &arg| acc + &format!("{arg:#01x}, "))));
                coll.push('\n');
            }
        }

        write!(f, "{}", coll)
    }
}

impl BasicBlock {
    fn ghetto_serialize_liveness(&self) -> String {
        fn live_state_json(state: &LiveState) -> String {
            let mut sb = String::new();
            sb.push_str("{\"regs\": [");
            for (i, reg) in state.live_regs.iter().enumerate() {
                if i > 0 {
                    sb.push_str(", ");
                }
                sb.push_str(&format!("\"{reg:?}\""));
            }
            sb.push_str("], \"flags\": [");
            let mut first = true;
            for (mask, name) in FLAG_NAMES.iter() {
                if (state.live_flags & mask) != 0 {
                    if first {
                        first = false;
                    } else {
                        sb.push_str(", ");
                    }
                    sb.push_str(&format!("\"{name}\""));
                }
            }
            sb.push_str("]}");
            sb
        }

        let mut str = "".to_owned();
        str.push_str(&format!("\"{:#01x}\": {{", self.label));
        str.push('\n');

        str.push_str(&format!("\"Liveness in\" : {},", live_state_json(&self.live_in)));
        str.push('\n');

        str.push_str(&format!("\"Liveness out\" : {},", live_state_json(&self.live_out)));
        str.push('\n');

        str.push_str("\"Instr Liveness\" : {");
        str.push('\n');

        for (i, (label, liveness)) in self.liveness_map.iter().enumerate() {
            if i > 0 {
                str.push_str(",\n");
            }
            str.push_str(&format!("\"{:#01x}\" : {}", label, live_state_json(&liveness)));
        }

        str.push('}');
        str.push('\n');

        str.push_str("}");
        str.push('\n');

        str
    }
}

fn main() -> Result<()> {
    let riscvm_target = AnalysisTarget::from_pe_with_export(Path::new("riscvm.exe"), "riscvm_run")?;
    let risc_vm_run_analysis = riscvm_target.analyze();
    {
        let dot_gr = Dot::new(&risc_vm_run_analysis.c_flow_graph).to_string().replace("digraph {\n", "digraph {\n    node [margin=0.1 shape=rect style=filled]\n").replace("not_taken\" ]", "\" color=\"red\"]").replace("taken\" ]", "\" color=\"green\"]");
        _ = fs::remove_file("dotgraph.dot");
        fs::write("dotgraph.dot", dot_gr).expect("Unable to write file");
    } // Dot graph

    let mut json = "{".to_owned();
    for b in &risc_vm_run_analysis.blocks {
        json.push_str(&b.ghetto_serialize_liveness().to_string());
        if b.label != risc_vm_run_analysis.blocks.iter().last().unwrap().label {
            json.push(',');
        }
    }
    json.push('}');

    fs::write("out.json", json).expect("Unable to write json file");

    let mut assembler = CodeAssembler::new(riscvm_target.architecture)?;
    let labels: Vec<_> = risc_vm_run_analysis.instructions.iter().map(|i| i.ip()).collect();
    for b in &risc_vm_run_analysis.blocks {
        for ins in &b.instructions {
            let l_state = b.liveness_map.get(&ins.ip()).unwrap();

            let unused_gprs: Vec<_> = (53..=68).map(|r_e| Register::try_from(r_e).unwrap().full_register()).filter(|r| !b.liveness_map.get(&ins.ip()).unwrap_or(&LiveState { live_flags: 0, live_regs: HashSet::new() }).live_regs.contains(r)).collect();

            if !unused_gprs.is_empty() && l_state.live_flags == RflagsBits::NONE && !l_state.live_regs.is_empty() {
                let chosen_reg = *unused_gprs.choose(&mut thread_rng()).unwrap();
                assembler.add_instruction(Instruction::with2(Code::Cmp_rm64_imm32, chosen_reg, random::<i32>())?)?;
                assembler.add_instruction(Instruction::with_branch(Code::Jne_rel32_64, ins.ip())?)?;
                for reg in unused_gprs {
                    assembler.add_instruction(Instruction::with2(Code::Cmp_r64_rm64, *l_state.live_regs.iter().choose(&mut thread_rng()).unwrap(), reg)?)?;
                    match thread_rng().gen_range(0..4) {
                        0 => assembler.add_instruction(Instruction::with_branch(Code::Jmp_rel32_64, *labels.choose(&mut thread_rng()).unwrap())?)?,

                        1 => assembler.add_instruction(Instruction::with_branch(Code::Jne_rel32_64, *labels.choose(&mut thread_rng()).unwrap())?)?,

                        2 => assembler.add_instruction(Instruction::with_branch(Code::Jg_rel32_64, *labels.choose(&mut thread_rng()).unwrap())?)?,

                        3 => assembler.add_instruction(Instruction::with_branch(Code::Jle_rel32_64, *labels.choose(&mut thread_rng()).unwrap())?)?,

                        4 => assembler.add_instruction(Instruction::with_branch(Code::Jae_rel32_64, *labels.choose(&mut thread_rng()).unwrap())?)?,
                        _ => {}
                    }
                }
            }
            assembler.add_instruction(*ins)?;
        }
    }

    let obfuscated_vm = assembler.assemble(0)?;
    fs::write("out.bin", obfuscated_vm.clone()).expect("Unable to write file");


    let isa_tests: Vec<(&str, usize, Vec<u8>)> = include!("..\\isa-tests\\isa.rs");

    let mut payload = fs::read(Path::new("payload.bin"))?;

    let mut vm_stack: [u8; 0x10000] = [0; 0x10000];

    unsafe {
        #[derive(Debug)]
        #[repr(C)]
        struct Riscvm {
            pc: i64,
            regs: [u64; 32],
        }
        let vm_page = windows_sys::Win32::System::Memory::VirtualAlloc(null_mut(), obfuscated_vm.len(), MEM_COMMIT, PAGE_EXECUTE_READWRITE);
        if vm_page.is_null() {
            panic!("virtualalloc failed: {}!", windows_sys::Win32::Foundation::GetLastError());
        }
        copy(obfuscated_vm.as_ptr(), vm_page.cast(), obfuscated_vm.len());
        type RunVm = extern "cdecl" fn(*mut Riscvm);
        let risc_vm_run: RunVm = std::mem::transmute(vm_page);
        println!("Doing isa-tests:");

        let biggest_test = isa_tests.iter().fold(0, |acc, item| {
            let (_, _, v) = item;
            acc.max(v.len())
        });
        let test_page = windows_sys::Win32::System::Memory::VirtualAlloc(null_mut(), biggest_test, MEM_COMMIT, PAGE_READWRITE);
        if test_page.is_null() {
            panic!("virtualalloc failed: {}!", windows_sys::Win32::Foundation::GetLastError());
        }
        let mut p_test = 0;
        for test in &isa_tests {
            let (name, offset, data) = test;
            copy(data.as_ptr(), test_page.cast(), data.len());
            let mut context = Riscvm { pc: test_page.wrapping_add(*offset) as i64, regs: [0; 32] };
            context.regs[2] = vm_stack.as_mut_ptr() as u64;

            context.regs[10] = 0;
            risc_vm_run(std::ptr::addr_of_mut!(context));
            println!("{name:<16}: {}", if context.regs[10] == 0 {
                "passed"
            } else {
                "FAILED"
            });
            if context.regs[10] == 0 {
                p_test += 1;
            }
        }
        if !isa_tests.is_empty() {
            println!("Passed {p_test}/{}, {}%", isa_tests.len(), p_test / isa_tests.len() * 100);
        }

        let mut context = Riscvm { pc: payload.as_mut_ptr() as i64, regs: [0; 32] };
        context.regs[2] = vm_stack.as_mut_ptr() as u64;
        risc_vm_run(std::ptr::addr_of_mut!(context));
    }

    Ok(())
}
