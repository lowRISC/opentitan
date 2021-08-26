System and Tool Requirements
============================

The Ibex CPU core is written in SystemVerilog.
We try to achieve a balance between the used language features (as described in our `style guide <https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md>`_) and reasonably wide tool support.

The following tools are known to work with the RTL code of Ibex.
Please `file an issue <https://github.com/lowRISC/ibex/issues>`_ if you experience problems with any of the listed tools, or if you have successfully used a tool with Ibex which is not listed here.

- Synopsys Design Compiler
- Xilinx Vivado, version |tool_requirements.vivado| and up.
- Verilator, version |tool_requirements.verilator| and up.
- Synopsys VCS, version at least |tool_requirements.vcs|.
- Cadence Incisive/Xcelium
- Mentor Questa
- Aldec Riviera Pro

To run the UVM testbench a RTL simulator which supports SystemVerilog and UVM 1.2 is required.
The `documentation of riscv-dv <https://github.com/google/riscv-dv#prerequisites>`_ contains a list of supported simulators.

To compile code that runs on Ibex, you'll need a RISC-V toolchain.
This isn't part of the core as such, but is necessary for verification.
See the :doc:`Verification <../03_reference/verification>` section of the Reference Guide for more details about which toolchains the project currently uses for testing.

Tools with known issues
-----------------------

Not all EDA tools have enough SystemVerilog support to be able to work with the Ibex code base.
Users of such tools are encouraged to file issues with the vendor.
As a workaround, tools like `sv2v <https://github.com/zachjs/sv2v>`_ can pre-process the source code to an older version of Verilog.

- Intel (Altera) Quartus Prime Lite and Standard are *not* supported due to insufficient SystemVerilog support
  (`issue #117 <https://github.com/lowRISC/ibex/issues/117>`_).
- Yosys cannot be used directly due to insufficient SystemVerilog support
  (`issue #60 <https://github.com/lowRISC/ibex/issues/60>`_).
  The ``syn`` folder in the Ibex repository contains scripts to use sv2v together with Yosys.
- Icarus Verilog is not supported due to insufficient SystemVerilog support.
