.. _instruction-decode-execute:

Instruction Decode and Execute
==============================

.. figure:: images/de_ex_stage.svg
   :name: de_ex_stage
   :align: center

   Instruction Decode and Execute

The Instruction Decode and Execute stage takes instruction data from the instruction fetch stage (which has been converted to the uncompressed representation in the compressed instruction case).
The instructions are decoded and executed all within one cycle including the register read and write.
The stage is made up of multiple sub-blocks which are described below.

Instruction Decode Block (ID)
-----------------------------
Source File: :file:`rtl/ibex_id_stage.sv`

The Instruction Decode (ID) controls the overall decode/execution process.
It contains the muxes to choose what is sent to the ALU inputs and where the write data for the register file comes from.
A small state machine is used to control multi-cycle instructions (see :ref:`pipeline-details` for more details), which stalls the whole stage whilst a multi-cycle instruction is executing.

Controller
----------
Source File: :file:`rtl/ibex_controller.sv`

The Controller contains the state machine that controls the overall execution of the processor.
It is responsible for:

* Handling core startup from reset
* Setting the PC for the IF stage on jump/branch
* Dealing with exceptions/interrupts (jump to appropriate PC, set relevant CSR values)
* Controlling sleep/wakeup on WFI
* Debugging control

Decoder
-------
Source File: :file:`rtl/ibex_decoder.sv`

The decoder takes uncompressed instruction data and issues appropriate control signals to the other blocks to execute the instruction.

Register File
-------------
Source Files: :file:`rtl/ibex_register_file_ff.sv` :file:`rtl/ibex_register_file_fpga.sv` :file:`rtl/ibex_register_file_latch.sv`

See :ref:`register-file` for more details.

Execute Block
-------------
Source File: :file:`rtl/ibex_ex_block.sv`

The execute block contains the ALU and the multiplier/divider blocks, it does little beyond wiring and instantiating these blocks.

Arithmetic Logic Unit (ALU)
---------------------------
Source File: :file:`rtl/ibex_alu.sv`

The Arithmetic Logic Logic (ALU) is a purely combinational block that implements operations required for the Integer Computational Instructions and the comparison operations required for the Control Transfer Instructions in the RV32I RISC-V Specification.
Other blocks use the ALU for the following tasks:

* Mult/Div uses it to perform addition as part of the multiplication and division algorithms
* It computes branch targets with a PC + Imm calculation
* It computes memory addresses for loads and stores with a Reg + Imm calculation
* The LSU uses it to increment addresses when performing two accesses to handle an unaligned access

Bit-Manipulation Extension
  Support for the `RISC-V Bit-Manipulation Extension version 1.0.0 <https://github.com/riscv/riscv-bitmanip/releases/download/1.0.0/bitmanip-1.0.0-38-g865e7a7.pdf>`_ and `draft version 0.93 from January 10, 2021 <https://github.com/riscv/riscv-bitmanip/blob/master/bitmanip-0.93.pdf>`_ is optional. [#B_draft]_
  It can be enabled via the enumerated parameter ``RV32B`` defined in :file:`rtl/ibex_pkg.sv`.
  By default, this parameter is set to "ibex_pkg::RV32BNone" to disable the bit-manipulation extension.

  There are three versions of the bit-manipulation extension available:
  The balanced version comprises a set of sub-extensions aiming for good benefits at a reasonable area overhead.
  It can be selected by setting the ``RV32B`` parameter to "ibex_pkg::RV32BBalanced".
  The OTEarlGrey version comprises all sub-extensions except for the Zbe.
  This version can be selected by setting the ``RV32B`` parameter to "ibex_pkg::RV32BOTEarlGrey".
  The full version comprises all sub-extensions and can be selected by setting the ``RV32B`` parameter to "ibex_pkg::RV32BFull".
  The following table gives an overview of which sub-extensions are implemented in each version and of which instructions are implemented as multi-cycle instructions.
  Multi-cycle instructions are completed in 2 cycles.
  All remaining instructions complete in a single cycle.

  +--------------------------------+---------+----------+------------+------+--------------------+
  | Bit-Manipulation Sub-Extension | Spec.   | Balanced | OTEarlGrey | Full | Multi-Cycle Instr. |
  +================================+=========+==========+============+======+====================+
  | Zba (Address generation)       | v.1.0.0 |    X     |     X      |  X   | None               |
  +--------------------------------+---------+----------+------------+------+--------------------+
  | Zbb (Base)                     | v.1.0.0 |    X     |     X      |  X   | rol, ror[i]        |
  +--------------------------------+---------+----------+------------+------+--------------------+
  | Zbc (Carry-less multiply)      | v.1.0.0 |          |     X      |  X   | None               |
  +--------------------------------+---------+----------+------------+------+--------------------+
  | Zbs (Single-bit)               | v.1.0.0 |    X     |     X      |  X   | None               |
  +--------------------------------+---------+----------+------------+------+--------------------+
  | Zbe (Bit compress/decompress)  | v.0.93  |          |            |  X   | All                |
  +--------------------------------+---------+----------+------------+------+--------------------+
  | Zbf (Bit-field place)          | v.0.93  |    X     |     X      |  X   | All                |
  +--------------------------------+---------+----------+------------+------+--------------------+
  | Zbp (Permutation)              | v.0.93  |          |     X      |  X   | None               |
  +--------------------------------+---------+----------+------------+------+--------------------+
  | Zbr (CRC)                      | v.0.93  |          |     X      |  X   | All                |
  +--------------------------------+---------+----------+------------+------+--------------------+
  | Zbt (Ternary)                  | v.0.93  |    X     |     X      |  X   | All                |
  +--------------------------------+---------+----------+------------+------+--------------------+

  The implementation of the Bit-Manipulation Extension comes with an area overhead of 2.7 kGE for the balanced version, 6.1 kGE for the OTEarlGrey version, and 7.5 kGE for the full version.
  These numbers were obtained by synthesizing the design with Yosys and relaxed timing constraints.


.. _mult-div:

Multiplier/Divider Block (MULT/DIV)
-----------------------------------
Source Files: :file:`rtl/ibex_multdiv_slow.sv` :file:`rtl/ibex_multdiv_fast.sv`

The Multiplier/Divider (MULT/DIV) is a state machine driven block to perform multiplication and division.
The fast and slow versions differ in multiplier only. All versions implement the same form of long division algorithm. The ALU block is used by the long division algorithm in all versions.

Multiplier
  The multiplier can be implemented in three variants controlled via the enumerated parameter ``RV32M`` defined in :file:`rtl/ibex_pkg.sv`.

  Single-Cycle Multiplier
    This implementation is chosen by setting the ``RV32M`` parameter to "ibex_pkg::RV32MSingleCycle".
    The single-cycle multiplier makes use of three parallel multiplier units, designed to be mapped to hardware multiplier primitives on FPGAs.
    It is therefore the **first choice for FPGA synthesis**.

    - Using three parallel 17-bit x 17-bit multiplication units and a 34-bit accumulator, it completes a MUL instruction in 1 cycle. MULH is completed in 2 cycles.
    - This MAC is internal to the mult/div block (no external ALU use).
    - Beware it is simply implemented with the ``*`` and ``+`` operators so results heavily depend upon the synthesis tool used.
    - ASIC synthesis has not yet been tested but is expected to consume 3-4x the area of the fast multiplier for ASIC.

  Fast Multi-Cycle Multiplier
    This implementation is chosen by setting the ``RV32M`` parameter to "ibex_pkg::RV32MFast".
    The fast multi-cycle multiplier provides a reasonable trade-off between area and performance. It is the **first choice for ASIC synthesis**.

    - Completes multiply in 3-4 cycles using a MAC (multiply accumulate) which is capable of a 17-bit x 17-bit multiplication with a 34-bit accumulator.
    - A MUL instruction takes 3 cycles, MULH takes 4.
    - This MAC is internal to the mult/div block (no external ALU use).
    - Beware it is simply implemented with the ``*`` and ``+`` operators so results heavily depend upon the synthesis tool used.
    - In some cases it may be desirable to replace this with a specific implementation such as an explicit gate level implementation.

  Slow Multi-Cycle Multiplier
    To select the slow multi-cycle multiplier, set the ``RV32M`` parameter to "ibex_pkg::RV32MSlow".

    - Completes multiply in clog2(``op_b``) + 1 cycles (for MUL) or 33 cycles (for MULH) using a Baugh-Wooley multiplier.
    - The ALU block is used to compute additions.

Divider
  Both the fast and slow blocks use the same long division algorithm, it takes 37 cycles to compute (though only requires 2 cycles when there is a divide by 0) and proceeds as follows:

    - Cycle 0: Check for divide by 0
    - Cycle 1: Compute absolute value of operand A (or return result on divide by 0)
    - Cycle 2: Compute absolute value of operand B
    - Cycles 4 - 36: Perform long division as described here: https://en.wikipedia.org/wiki/Division_algorithm#Integer_division_(unsigned)_with_remainder.

By setting the ``RV32M`` parameter to "ibex_pkg::RV32MNone", the M-extension can be disabled completely.

Control and Status Register Block (CSR)
---------------------------------------
Source File: :file:`rtl/ibex_cs_registers.sv`

The CSR contains all of the CSRs (control/status registers).
Any CSR read/write is handled through this block.
Performance counters are held in this block and incremented when appropriate (this includes ``mcycle`` and ``minstret``).
Read data from a CSR is available the same cycle it is requested.
Further detail on the implemented CSRs can be found in :ref:`cs-registers`

Load-Store Unit (LSU)
---------------------
Source File: :file:`rtl/ibex_load_store_unit.sv`

The Load-Store Unit (LSU) interfaces with main memory to perform load and store operations.
See :ref:`load-store-unit` for more details.

.. rubric:: Footnotes

.. [#B_draft] Ibex fully implements the ratified version 1.0.0 of the RISC-V Bit-Manipulation Extension including the Zba, Zbb, Zbc and Zbs sub-extensions.
   In addition, Ibex also supports the remaining Zbe, Zbf, Zbp, Zbr and Zbt sub-extensions as defined in draft version 0.93 of the RISC-V Bit-Manipulation Extension.
   Note that the latter sub-extensions may change before being ratified as a standard by the RISC-V Foundation.
   Ibex will be updated to match future versions of the specification.
   Prior to ratification this may involve backwards incompatible changes.
   Additionally, neither GCC or Clang have committed to maintaining support upstream for unratified versions of the specification.
