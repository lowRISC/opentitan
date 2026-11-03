# RISC-V Debug Support for various Cores

This module is an implementation of a debug unit compliant with the [RISC-V
debug specification](https://github.com/riscv/riscv-debug-spec) v0.13.1. It is
used in the [cva6](https://github.com/pulp-platform/cva6),
[cv32e40p](https://github.com/pulp-platform/cv32e40p) and
[ibex](https://github.com/lowRISC/ibex) cores.

## Implementation
We use an execution-based technique, also described in the specification, where
the core is running in a "park loop". Depending on the request made to the debug
unit via JTAG over the Debug Transport Module (DTM), the code that is being
executed is changed dynamically. This approach simplifies the implementation
side of the core, but means that the core is in fact always busy looping while
debugging.

## Features
The following features are currently supported

* Parametrizable buswidth for `XLEN=32` `XLEN=64` cores
* Accessing registers over abstract command
* Program buffer
* System bus access (only `XLEN`)
* DTM with JTAG interface

These are not implemented (yet)

* Trigger module
* Quick access using abstract commands
* Accessing memory using abstract commands
* Authentication

## Limitations
* The JTAG clock frequency needs to be lower than the system's clock frequency (see also https://github.com/pulp-platform/riscv-dbg/issues/163). 

## Tests

We use OpenOCD's [RISC-V compliance
tests](https://github.com/riscv/riscv-openocd/blob/riscv/src/target/riscv/riscv-013.c),
our custom testbench in `tb/` and
[riscv-tests/debug](https://github.com/riscv/riscv-tests/tree/master/debug).
