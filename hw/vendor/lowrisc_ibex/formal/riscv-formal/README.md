# Formal

**Unsupported Verilog source creation for RISC-V Formal Verification.**

The Verilog source created here is used by [riscv-formal](https://github.com/SymbioticEDA/riscv-formal).

Riscv-formal uses Yosys, but the SystemVerilog front-end of Yosys does not support all the language features used by Ibex.
The `Makefile` provided here uses sv2v and Yosys to create a single Verilog source of Ibex.

This flow has some similarities to [syn](../syn/README.md), but uses only a simplified subset.

In order to make it easier to use with riscv-formal, the conversion is done with a simple `Makefile`.

## Prerequisites

Install the following, if not used with the container flow described in riscv-formal.

  - [sv2v](https://github.com/zachjs/sv2v), best option is to use the latest version, but [packed arrays](https://github.com/zachjs/sv2v/commit/aea64e903cd0ff8e8437cae7f989e8bc29ac01a2) is required
  - [Yosys](https://github.com/YosysHQ/yosys)

## Limitations

The "M" extension is currently disabled.

## Usage

It should not be necessary to create the Verilog source manually as it is used by the riscv-formal Ibex build system.

Run the following command from the top level directory of Ibex to create the Verilog source.

```console
make -C formal/riscv-formal
```

This will create a directory *formal/riscv-formal/build* which contains an equivalent Verilog file for each SystemVerilog source.
The single output file *formal/riscv-formal/ibex.v* contains the complete Ibex source, which can then be imported by riscv-formal.
