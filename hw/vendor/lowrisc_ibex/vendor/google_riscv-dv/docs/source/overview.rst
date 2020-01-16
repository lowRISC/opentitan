Overview
========

RISCV-DV is a SV/UVM based open-source instruction generator for RISC-V
processor verification. It currently supports the following features:

- Supported instruction set: RV32IMAFDC, RV64IMAFDC
- Supported privileged mode: machine mode, supervisor mode, user mode
- Page table randomization and exception
- Privileged CSR setup randomization
- Privileged CSR test suite
- Trap/interrupt handling
- Test suite to stress test MMU
- Sub-program generation and random program calls
- Illegal instruction and HINT instruction generation
- Random forward/backward branch instructions
- Supports mixing directed instructions with random instruction stream
- Debug mode support, with fully randomized debug ROM
- Instruction generation coverage model
- Communication of information to any integrated SV testbench
- Co-simulation with multiple ISS : spike, riscv-ovpsim

A CSR test generation script written in Python is also provided, to generate a
directed test suite that stresses all CSR instructions on all of the CSRs that
the core implements.
