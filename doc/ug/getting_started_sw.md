# Build Software

## Prerequisites

_Make sure you followed the install instructions to [prepare the system](install_instructions.html#system-preparation) and install the [compiler toolchain](install_instructions.html#compiler-toolchain)._

## Building software

```console
$ cd $REPO_TOP/sw/hello_world
$ make CC=/tools/riscv/bin/riscv32-unknown-elf-gcc
```

The build process produces a variety of output files.

* `.elf`: the linked program in ELF format
* `.bin`: the linked program as plain binary
* `.dis`: the disassembled program
* `.vmem`: a Verilog memory file which can be read by `$readmemh()` in Verilog code
