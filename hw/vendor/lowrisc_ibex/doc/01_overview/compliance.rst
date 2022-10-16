Standards Compliance
====================

Ibex is a standards-compliant 32 bit RISC-V processor.
It follows these specifications:

* `RISC-V Instruction Set Manual, Volume I: User-Level ISA, document version 20190608-Base-Ratified (June 8, 2019) <https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMFDQC-and-Priv-v1.11/riscv-spec-20190608.pdf>`_
* `RISC-V Instruction Set Manual, Volume II: Privileged Architecture, document version 20211203 (December 4, 2021) <https://github.com/riscv/riscv-isa-manual/releases/download/Priv-v1.12/riscv-privileged-20211203.pdf>`_.
  Ibex implements the Machine ISA version 1.12.
* `RISC-V External Debug Support, version 0.13.2 <https://content.riscv.org/wp-content/uploads/2019/03/riscv-debug-release.pdf>`_
* `RISC-V Bit-Manipulation Extension, version 1.0.0 <https://github.com/riscv/riscv-bitmanip/releases/download/1.0.0/bitmanip-1.0.0-38-g865e7a7.pdf>`_ and `version 0.93 (draft from January 10, 2021) <https://github.com/riscv/riscv-bitmanip/blob/master/bitmanip-0.93.pdf>`_
* `PMP Enhancements for memory access and execution prevention on Machine mode (Smepmp) version 0.9.3 <https://github.com/riscv/riscv-tee/blob/61455747230a26002d741f64879dd78cc9689323/Smepmp/Smepmp.pdf>`_

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

   * - **B**: Standard Extension for Bit-Manipulation Instructions
     - 1.0.0 + 0.93 [#B_draft]_
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

See :ref:`PMP Enhancements<pmp-enhancements>` for more information on Ibex's experimental and optional support for the PMP Enhancement proposal from the Trusted Execution Environment (TEE) working group.

.. rubric:: Footnotes

.. [#B_draft] Ibex fully implements the ratified version 1.0.0 of the RISC-V Bit-Manipulation Extension including the Zba, Zbb, Zbc and Zbs sub-extensions.
   In addition, Ibex also supports the remaining Zbe, Zbf, Zbp, Zbr and Zbt sub-extensions as defined in draft version 0.93 of the RISC-V Bit-Manipulation Extension.
   Note that the latter sub-extensions may change before being ratified as a standard by the RISC-V Foundation.
   Ibex will be updated to match future versions of the specification.
   Prior to ratification this may involve backwards incompatible changes.
   Additionally, neither GCC or Clang have committed to maintaining support upstream for unratified versions of the specification.
