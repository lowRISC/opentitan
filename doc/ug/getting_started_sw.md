# Build Software

## Prerequisites

_Make sure you followed the install instructions to [prepare the system]({{< relref "install_instructions#system-preparation" >}}) and install the [compiler toolchain]({{< relref "install_instructions#compiler-toolchain" >}})._

## Building software

```console
$ cd $REPO_TOP/sw
$ make SW_DIR=examples/hello_world CC=/tools/riscv/bin/riscv32-unknown-elf-gcc
```

The build process produces a variety of output files.

* `.elf`: the linked program in ELF format
* `.bin`: the linked program as plain binary
* `.dis`: the disassembled program
* `.vmem`: a Verilog memory file which can be read by `$readmemh()` in Verilog code

Please see [SW build flow]("/sw/doc/sw_build_flow.md") for more details.
