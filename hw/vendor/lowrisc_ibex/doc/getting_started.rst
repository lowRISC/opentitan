.. _getting-started:

Getting Started with Ibex
=========================

This page discusses initial steps and requirements to start using Ibex in your design.

Register File
-------------

Ibex comes with three different register file implementations that can be selected using the enumerated parameter ``RegFile`` defined in :file:`rtl/ibex_pkg.sv`.
Depending on the target technology, either the flip-flop-based ("ibex_pkg::RegFileFF", default), the latch-based ("ibex_pkg::RegFileLatch") or an FPGA-targeted ("ibex_pkg::RegFileFPGA") implementation should be selected.
For more information about the three register file implementations and their trade-offs, check out :ref:`register-file`.
