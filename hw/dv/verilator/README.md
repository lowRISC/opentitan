# Verilator memory loading support

## ELF support

### BSS sections

When loading ELF files into the memory, only the data stored in the file is loaded into the memory.
Data specified by the memory size is not set.
This is the case for BSS sections for which only the size information is stored in the ELF file.
The zero-ing of this sections is the responsibility of the executed code.
This is typically achieved by setting symbols for the start and end of the BSS section in the linker script and zero-ing the intermediate addresses by the startup routine.

**Requirement: BSS zero-ing must be implemented by the executed software.**
