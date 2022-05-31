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

For specific formatting and secure coding guidelines, see the [OTBN style guide]({{< relref "doc/rm/otbn_style_guide" >}}).

## The tools

### Assembler

The OTBN assembler is called `otbn_as.py` and can be found at `hw/ip/otbn/util/otbn_as.py`.
This has the same command line interface as `riscv32-unknown-elf-as` (indeed, it's a wrapper around that program).
The only difference in default flags is that `otbn_as.py` passes `-mno-relax`, telling the assembler not to request linker relaxation.
This is needed because one of these relaxations generates GP-relative loads, which assume `x3` is treated as a global pointer (not true for OTBN code).

To assemble some code in `foo.s` to an ELF object called `foo.o`, run:
```shell
hw/ip/otbn/util/otbn_as.py -o foo.o foo.s
```

### Linker

The OTBN linker is called `otbn_ld.py` and can be found at `hw/ip/otbn/util/otbn_ld.py`.
This is a thin wrapper around `riscv32-unknown-elf-ld`, but supplies a default linker script that matches the OTBN memory layout.
This linker script creates `.start`, `.text` and `.data` output sections.
The `.start` and `.text` sections go to IMEM, with `.start` coming first.
The `.data` section goes to DMEM.
Since OTBN has a strict Harvard architecture with IMEM and DMEM both starting at address zero, the `.start` and the `.data` sections will both start at VMA zero.
The instruction and data segments have distinct LMAs (for addresses, see the IMEM and DMEM windows at `hw/ip/otbn/data/otbn.hjson`).

Since the entry point for OTBN is always address zero, the entry vector should be the one and only thing in the `.start` section.
To achieve that, put your entry point (and nothing else) in the `.text.start` input section like this:
```asm
.section .text.start
  jal x0, main

.text
  ...
```
This ensure that, even if there are multiple objects being linked together, the intended entry point will appear in the right place.

To link ELF object files to an OTBN ELF binary, run
```shell
hw/ip/otbn/util/otbn_ld.py -o foo foo0.o foo1.o foo2.o
```

### Objdump

To disassemble OTBN code, use `otbn_objdump.py`, which can be found at `hw/ip/otbn/util/otbn_objdump.py`.
This wraps `riscv32-unknown-elf-objdump`, but correctly disassembles OTBN instructions when run with the `-d` flag.

To disassemble the ELF binary linked in the previous section, run
```shell
hw/ip/otbn/util/otbn_objdump.py -d foo
```
