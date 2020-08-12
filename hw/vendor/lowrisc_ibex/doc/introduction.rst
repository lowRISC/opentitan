Introduction
============

.. figure:: images/blockdiagram.svg
   :name: blockdiagram

   Block Diagram

Ibex is a 2-stage in-order 32b RISC-V processor core.
Ibex has been designed to be small and efficient.
Via two parameters, the core is configurable to support four ISA configurations.
:numref:`blockdiagram` shows a block diagram of the core.

Standards Compliance
--------------------

Ibex is a standards-compliant 32b RISC-V processor.
It follows these specifications:

* `RISC-V Instruction Set Manual, Volume I: User-Level ISA, document version 20190608-Base-Ratified (June 8, 2019) <https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMFDQC-and-Priv-v1.11/riscv-spec-20190608.pdf>`_
* `RISC-V Instruction Set Manual, Volume II: Privileged Architecture, document version 20190608-Base-Ratified (June 8, 2019) <https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMFDQC-and-Priv-v1.11/riscv-privileged-20190608.pdf>`_.
  Ibex implements the Machine ISA version 1.11.
* `RISC-V External Debug Support, version 0.13.2 <https://content.riscv.org/wp-content/uploads/2019/03/riscv-debug-release.pdf>`_
* `RISC-V Bit Manipulation Extension, version 0.92 (draft from November 8, 2019) <https://github.com/riscv/riscv-bitmanip/blob/master/bitmanip-0.92.pdf>`_

Many features in the RISC-V specification are optional, and Ibex can be parametrized to enable or disable some of them.

Ibex can be parametrized to support either of the following two instruction sets.

* The RV32I Base Integer Instruction Set, version 2.1
* The RV32E Base Integer Instruction Set, version 1.9 (draft from June 8, 2019)

In addition, the following instruction set extensions are available.

.. list-table:: Ibex Instruction Set Extensions
   :header-rows: 1

   * - Extension
     - Version
     - Configurability

   * - **C**: Standard Extension for Compressed Instructions
     - 2.0
     - always enabled

   * - **M**: Standard Extension for Integer Multiplication and Division
     - 2.0
     - optional

   * - **B**: Draft Extension for Bit Manipulation Instructions
     - 0.92 [#B_draft]_
     - optional

   * - **Zicsr**: Control and Status Register Instructions
     - 2.0
     - always enabled

   * - **Zifencei**: Instruction-Fetch Fence
     - 2.0
     - always enabled

Most content of the RISC-V privileged specification is optional.
Ibex currently supports the following features according to the RISC-V Privileged Specification, version 1.11.

* M-Mode and U-Mode
* All CSRs listed in :ref:`cs-registers`
* Performance counters as described in :ref:`performance-counters`
* Vectorized trap handling as described at :ref:`exceptions-interrupts`

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

Contents
--------

 * :ref:`getting-started` discusses the requirements and initial steps to start using Ibex.
 * :ref:`core-integration` provides the instantiation template and gives descriptions of the design parameters as well as the input and output ports.
 * :ref:`pipeline-details` described the overal pipeline structure.
 * :ref:`instruction-decode-execute` describes how the Instruction Decode and Execute stage works.
 * The instruction and data interfaces of Ibex are explained in :ref:`instruction-fetch` and :ref:`load-store-unit`, respectively.
 * :ref:`icache` describes the optional Instruction Cache.
 * The two register-file flavors are described in :ref:`register-file`.
 * The control and status registers are explained in :ref:`cs-registers`.
 * :ref:`performance-counters` gives an overview of the performance monitors and event counters available in Ibex.
 * :ref:`exceptions-interrupts` deals with the infrastructure for handling exceptions and interrupts,
 * :ref:`pmp` gives a brief overview of PMP support.
 * :ref:`debug-support` gives a brief overview on the debug infrastructure.
 * :ref:`tracer` gives a brief overview of the tracer module.
 * For information regarding formal verification support, check out :ref:`rvfi`.
 * :ref:`examples` gives an overview of how Ibex can be used.


History
-------

Ibex development started in 2015 under the name "Zero-riscy" as part of the `PULP platform <https://pulp-platform.org>`_ for energy-efficient computing.
Much of the code was developed by simplifying the RV32 CPU core "RI5CY" to demonstrate how small a RISC-V CPU core could actually be `[1] <https://doi.org/10.1109/PATMOS.2017.8106976>`_.
To make it even smaller, support for the "E" extension was added under the code name "Micro-riscy".
In the PULP ecosystem, the core is used as the control core for PULP, PULPino and PULPissimo.

In December 2018 lowRISC took over the development of Zero-riscy and renamed it to Ibex.

References
----------

1. `Schiavone, Pasquale Davide, et al. "Slow and steady wins the race? A comparison of ultra-low-power RISC-V cores for Internet-of-Things applications." 27th International Symposium on Power and Timing Modeling, Optimization and Simulation (PATMOS 2017) <https://doi.org/10.1109/PATMOS.2017.8106976>`_

.. rubric:: Footnotes

.. [#B_draft] Note that while Ibex fully implements draft version 0.92 of the RISC-V Bit Manipulation Extension, this extension may change before being ratified as a standard by the RISC-V Foundation.
   Ibex will be updated to match future versions of the specification.
   Prior to ratification this may involve backwards incompatible changes.
   Additionally, neither GCC or Clang have committed to maintaining support upstream for unratified versions of the specification.
