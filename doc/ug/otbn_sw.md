---
title: "Writing and building software for OTBN"
---

OTBN is the OpenTitan Big Number accelerator and this document describes how to write and build software for it.
The [OTBN reference manual]({{< relref "hw/ip/otbn/doc" >}}) describes the hardware and associated ISA.

Since OTBN is designed for cryptographic offload, not general computation, it has no C compiler.
However, it does have the usual binutils programs: an assembler, linker and disassembler.
The core of OTBN's instruction set is based on RV32I, the RISC-V base integer instruction set.
As such, we implement the toolchain as a thin wrapper around RISC-V binutils.

## Assembly format and examples

The OTBN ISA and programmer model are described in the [OTBN reference manual]({{< relref "hw/ip/otbn/doc" >}}).
In particular, note that the register `x1` has special stack-like behaviour.
There are some example programs at `sw/otbn/code-snippets`.
These range from simple examples of how to use pseudo-operations up to example cryptographic primitives.

## The tools

### Assembler

The OTBN assembler is called `otbn-as` and can be found at `hw/ip/otbn/util/otbn-as`.
This has the same command line interface as `riscv32-unknown-elf-as` (indeed, it's a wrapper around that program).
The only difference in default flags is that `otbn-as` passes `-mno-relax`, telling the assembler not to request linker relaxation.
This is needed because one of these relaxations generates GP-relative loads, which assume `x3` is treated as a global pointer (not true for OTBN code).

To assemble some code in `foo.s` to an ELF object called `foo.o`, run:
```shell
hw/ip/otbn/util/otbn-as -o foo.o foo.s
```

### Linker

The OTBN linker is called `otbn-ld` and can be found at `hw/ip/otbn/util/otbn-ld`.
This is a thin wrapper around `riscv32-unknown-elf-ld`, but supplies a default linker script that matches the OTBN memory layout.
This linker script creates a `.text` and a `.data` section.
Since OTBN has a strict Harvard architecture (instructions and data both starting at address zero), the linker script places them both at VMA zero.
The instruction and data segments have distinct LMAs (for addresses, see the IMEM and DMEM windows at `hw/ip/otbn/data/otbn.hjson`).

To link ELF object files to an OTBN ELF binary, run
```shell
hw/ip/otbn/util/otbn-ld -o foo foo0.o foo1.o foo2.o
```

### Objdump

To disassemble OTBN code, use `otbn-objdump`, which can be found at `hw/ip/otbn/util/otbn-objdump`.
This wraps `riscv32-unknown-elf-objdump`, but correctly disassembles OTBN instructions when run with the `-d` flag.

To disassemble the ELF binary linked in the previous section, run
```shell
hw/ip/otbn/util/otbn-objdump -d foo
```
