use crate::BasicBlock;
use iced_x86::{FlowControl, Instruction};

type ImplIteratorMut<'a, Item> =
    ::std::iter::Chain<::std::slice::IterMut<'a, Item>, ::std::slice::IterMut<'a, Item>>;
pub trait SplitThisMut {
    type TypeItem;

    fn split_this_mut(
        self: &'_ mut Self,
        i: usize,
    ) -> (&'_ mut Self::TypeItem, ImplIteratorMut<'_, Self::TypeItem>);
}
impl<T> SplitThisMut for [T] {
    type TypeItem = T;

    fn split_this_mut(
        self: &'_ mut Self,
        i: usize,
    ) -> (&'_ mut Self::TypeItem, ImplIteratorMut<'_, Self::TypeItem>) {
        let (prev, current_and_end) = self.split_at_mut(i);
        let (current, end) = current_and_end.split_at_mut(1);
        (&mut current[0], prev.iter_mut().chain(end))
    }
}

pub trait BasicBlockVecExt {
    fn get_instruction_count(&self) -> usize;
    fn get_with_label(&self, index: u64) -> Option<&BasicBlock>;
    fn get_with_label_as_mut(&mut self, addr: u64) -> Option<&mut BasicBlock>;
}
impl BasicBlockVecExt for Vec<BasicBlock> {
    fn get_instruction_count(&self) -> usize {
        let mut count = 0;
        for b in self {
            count += b.instructions.len();
        }
        count
    }

    fn get_with_label(&self, addr: u64) -> Option<&BasicBlock> {
        self.iter().find(|&bb| bb.label == addr)
    }

    fn get_with_label_as_mut(&mut self, addr: u64) -> Option<&mut BasicBlock> {
        self.iter_mut().find(|bb| bb.label == addr)
    }
}
pub trait InstructionExt {
    fn get_possible_flows(&self) -> Vec<u64>;
}
impl InstructionExt for Instruction {
    fn get_possible_flows(&self) -> Vec<u64> {
        let mut edges = Vec::new();
        match self.flow_control() {
            FlowControl::UnconditionalBranch => {
                edges.push(self.near_branch_target());
            }
            FlowControl::ConditionalBranch => {
                let target = self.near_branch_target();
                let next = self.next_ip();
                edges.push(target);
                edges.push(next);
            }
            FlowControl::Next => {
                edges.push(self.next_ip());
            }
            _ => {}
        };
        edges
    }
}
