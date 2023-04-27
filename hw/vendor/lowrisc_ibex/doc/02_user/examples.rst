.. _examples:

Examples
========

There are two examples that demonstrate Ibex usage.

The first is 'Simple System' and is part of the Ibex repository.
It demonstrates a minimal system connecting Ibex to some memory with a timer peripheral and is targeted at simulation.

The second is the `'Ibex Demo System' <https://www.github.com/lowrisc/ibex-demo-system>`_ which is a separate repository.
It is targeted at FPGA implementation and contains some extra peripherals along with a RISC-V debug module integration.

Simple System
-------------

Simple system is built via FuseSoC.
Verilator is the primary simulator it is designed for, though other simulators are also supported (such as VCS).
Its aim is to make running a binary against Ibex RTL, obtaining an instruction trace, wave trace and any other simulation outputs as simple as possible along with demonstrating basic Ibex integration.
See the `Simple System README <https://github.com/lowRISC/ibex/tree/master/examples/simple_system>`_ for more information.

There is an extended version of simple system which adds co-simulation checking.
This cross-checks every instruction execution against a RISC-V ISS.
It is the same co-simulation method used by our full DV environment but enables its use in a far simpler setup.
The simple system co-simulation setup is compatible with Verilator (unlike our full DV environment).
See :ref:`cosim` for more information.

