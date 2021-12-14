.. _getting-started:

Getting Started with Ibex
=========================

This page discusses initial steps and requirements to start using Ibex in your design.

Register File
-------------

Ibex comes with three different register file implementations that can be selected using the enumerated parameter ``RegFile`` defined in :file:`rtl/ibex_pkg.sv`.
Depending on the target technology, either the flip-flop-based ("ibex_pkg::RegFileFF", default), the latch-based ("ibex_pkg::RegFileLatch") or an FPGA-targeted ("ibex_pkg::RegFileFPGA") implementation should be selected.
For more information about the three register file implementations and their trade-offs, check out :ref:`register-file`.

Identification CSRs
-------------------

The RISC-V Privileged Architecture specifies several read-only CSRs that identify the vendor and micro-architecture of a CPU.
These are ``mvendorid``, ``marchid`` and ``mimpid``.
The fixed, read-only values for these CSRs are defined in :file:`rtl/ibex_pkg.sv`.
Implementers should carefully consider appropriate values for these registers.
Ibex, as an open source implementation, has an assigned architecture ID (``marchid``) of 22.
(Allocations are specified in `marchid.md of the riscv-isa-manual repository <https://github.com/riscv/riscv-isa-manual/blob/master/marchid.md>`_.)
If significant changes are made to the micro-architecture a different architecture ID should be used.
The vendor ID and implementation ID (``mvendorid`` and ``mimpid``) both read as 0 by default, meaning non-implemented.
Implementers may wish to use other values here.
Please see the RISC-V Privileged Architecture specification for more details on what these IDs represent and how they should be chosen.
