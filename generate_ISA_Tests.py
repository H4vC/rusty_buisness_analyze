from elftools.elf.elffile import ELFFile
from elftools.elf.sections import SymbolTableSection
import os
import zlib

def parse_test_elf(file):
    with open(file, "rb") as f:
        elf = ELFFile(f)
        # Enumerate the SymbolTableSection
        for section in elf.iter_sections():
            if isinstance(section, SymbolTableSection):
                for i in range(section.num_symbols()):
                    symbol = section.get_symbol(i)
                    if symbol.name:
                        if symbol.name.startswith("test_"):
                            address = symbol.entry.st_value
                            # Convert address to file offset
                            offset = list(elf.address_offsets(address))[0]
                            return address, offset
    return None, None

def main():
    tests = []
    directory = "isa-tests"
    code = "import zlib\n\n"
    for file in sorted(os.listdir(directory)):
        if file.startswith("rv64") and not file.endswith(".dump"):
            path = os.path.join(directory, file)
            address, offset = parse_test_elf(path)
            if offset is None:
                print(f"Failed to parse {file}")
                continue
            data = f"__{file.replace('-', '_').upper()}_DATA = zlib.decompress(b\""
            with open(path, "rb") as f:
                for byte in zlib.compress(f.read(), 9):
                    data += f"\\x{byte:02x}"
            data += "\")\n"
            code += data
            tests.append((file, address, offset))

    code += "\n"

    code += "TESTS = [\n"
    for name, address, offset in tests:
        variable = f"__{name.replace('-', '_').upper()}_DATA"
        code += f"    (\"{name}\", {variable}, {hex(address)}, {hex(offset)}),\n"
    code += "]\n"

    with open("isa-tests/data.py", "wb") as f:
        f.write(code.encode("utf-8"))


if __name__ == "__main__":
    main()