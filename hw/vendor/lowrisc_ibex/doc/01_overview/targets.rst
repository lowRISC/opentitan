Synthesis Targets
=================

ASIC Synthesis
--------------

ASIC synthesis is supported for Ibex.
The whole design is completely synchronous and uses positive-edge triggered flip-flops, except for the register file, which can be implemented either with latches or with flip-flops.
See :ref:`register-file` for more details.
The core occupies an area of roughly 24 kGE when using the latch-based register file and implementing the RV32IMC ISA, or 16 kGE when implementing the RV32EC ISA.


FPGA Synthesis
--------------

FPGA Synthesis is supported for Ibex.
The FPGA-optimized register file implementation should be used.
The flip-flop based register file is also compatible with FPGA synthesis, however it may result in significantly higher resource utilization.
Since latches are not well supported on FPGAs, the latch-based register file should not be used.
