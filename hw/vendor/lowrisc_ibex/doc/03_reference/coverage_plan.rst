.. _coverage-plan:

Coverage Plan
=============

.. note::
  Work to implement the functional coverage described in this plan is on-going and the plan itself is not yet complete.

.. todo::
  Branch prediction hasn't yet been considered, this will add more coverage points and alter some others

Introduction
------------
Ibex functional coverage is split into two major categories:

* Architectural coverage - which is concerned with instructions being executed and exercising various features of the RISC-V architecture (e.g. PMP) and does not consider the details of how this execution occurs.
* Microarchitectural coverage - which is concerned with the specifics of the RTL operation, ensuring interesting corner cases are seen along with various micro-architectural events (e.g. the different kinds of stall) and combinations of them.

Architectural coverage is not Ibex specific. It can be determined directly from a trace of executed instructions and is handled by RISCV-DV, details can be found in the `RISCV-DV documentation <https://htmlpreview.github.io/?https://github.com/google/riscv-dv/blob/master/docs/build/singlehtml/index.html#document-coverage_model>`_.

Microarchitectural coverage will probe the Ibex RTL directly and is described here.
There is some inevitable overlap between architectural and microarchitectural coverage but we aim to minimise it.

Microarchitectural Events and Behaviour
---------------------------------------
Below are lists of specific things from the microarchitecture that will be included in functional coverage.
Each of the points listed below must be covered.
This will be further combined using cross coverage which is described in the section below.

Instructions
^^^^^^^^^^^^

Categories
""""""""""
``cp_id_instr_category``

Instructions can be grouped into a number of categories.
Each category exercises different data and control paths in the core.
For example the ``ADD`` and ``SUB`` instructions are in the same category as they are almost identical for the microarchitecture (both read two registers and write to one, both feed operands to the ALU and take their result from it, both have the same response to interrupts etc; the only difference is the ALU operation).

Instructions can be compressed or uncompressed but that isn't factored into the instruction categories below (excepting for illegal instructions).
The decompression occurs in the IF stage and is invisible to the ID/EX stage so isn't relevant for instruction execution.
A separate set of category-agnostic compressed instruction behaviour is considered instead.

An instruction category is sampled at the ID/EX stage (which is where all the varying behaviours actually occur).
Some categories are just a single instruction, which is named without further description.


* **ALU** - All of the reg/reg reg/imm instructions that use the ALU.
  This is any RISC-V instruction with an opcode of ``7'b0010011`` or ``7'b0110011`` (``ibex_pkg::OPCODE_OP`` and ``ibex_pkg::OPCODE_OP_IMM``) other than the ``MUL*`` and ``DIV*`` family of instructions (from RV32M).
* **Mul** - Any ``MUL*`` instruction (from RV32M).
* **Div** - Any ``DIV*`` instruction (from RV32M).
* **Branch** - Any ``B*`` family branch instruction.
* **Jump** - ``JAL``/``JALR``
* **Load** - Any ``L*`` family load instruction.
* **Store** - Any ``S*`` family load instruction.
* **CSRAccess** - Any instruction from Zicsr.
* **EBreakDbg**/**EBreakExc** - An ``EBREAK`` instruction that either enters debug mode (Dbg) or causes an exception (Exc).
  Which occurs depends upon the setting of ``dcsr.ebreakm`` / ``dcsr.ebreaku`` combined with the privilege level of executed instruction.
* ``ECALL``
* ``MRET``
* ``DRET``
* ``WFI``
* ``FENCE``
* ``FENCE.I``
* **FetchError** - Any instruction that saw a fetch error.
* **CompressedIllegal** - Any compressed instruction with an illegal encoding.
* **UncompressedIllegal** - Any uncompressed instruction with an illegal encoding.
* **CSRIllegal** - Any instruction attempting a CSR access that is not allowed.
* **PrivIllegal** - Illegal due to privilege level or being in/out of debug mode.
* **OtherIllegal** - Any other instruction that raises an Illegal instruction exception that isn't in the other categories.
* **None** - No instruction in ID/EX stage.

Stalls
""""""
``cp_stall_type_id``

Not all instructions can see all kinds of stalls.
A stall category is sampled at the ID/EX stage only (as stalls in IF and WB don't break down into categories).

* **Instr** - A stall caused by a multi-cycle instruction.
  This can be seen by instructions from categories:

  * **MUL**
  * **DIV**
  * **Branch**
  * **Jump**

* **LdHz** - A load hazard, the instruction in ID/EX depends upon the result of a load that is awaiting a response in writeback.
  This can be seen by instructions from categories:

  * **ALU**
  * **Mul**
  * **Div**
  * **Branch**
  * **Jump**
  * **Load**
  * **Store**
  * **CSRAccess**

* **Mem** - Memory stall, the instruction in ID/EX is awaiting a prior memory request to complete before it can begin (to allow precise interrupts on a memory error response). This can be seen for all instruction categories

Privilege Level
"""""""""""""""
Ibex can operate at either the M (machine) or U (user) privilege levels.
Different aspects of the Ibex microarchitecture can be using different privilege levels at once.

* ``cp_priv_mode_id`` - Privilege level of ID/EX stage instruction.
* ``cp_priv_mode_lsu`` - Privilege level of LSU operation (ID/EX privilege level modified by ``mstatus.mprv`` and ``mstatus.mpp`` settings).

Note that the privilege level of the instruction in WB isn't retained by the microarchitecture and is not relevant to coverage.
The privilege level of the IF instruction is effectively unknown.
The instruction is checked when moving from IF to ID/EX against the ID stage privilege level to check if execution is permitted by PMP.
Any instruction that reaches WB can be considered bound to retire and any relevant checks and functionality altered by the privilege mode is dealt with at an earlier stage.

Hazards
"""""""
Ibex hazards all occur in the interaction between the ID and EX stage.

* RAW Reg - Read after write hazard, instruction in ID/EX reads a register that writeback is writing.
  Split into two versions:

  * RAW load - Instruction in ID/EX reading from destination of load in writeback.
    Produces a stall (Category LdHz) and shouldn't forward data.
    Covered by ``cp_stall_type_id``
  * ``cp_wb_reg_no_load_hz`` - Instruction in writeback isn't a load.
    Handled with data forwarding and no stall.

* RAW Load/Store bytes - Load with bytes overlapping a store immediately before it.

State Specific Behaviour
""""""""""""""""""""""""
Some instructions will behave differently depending upon the state of the processor (e.g. the privilege level the instruction executes at, CSR settings or whether the processor is in debug mode).

* Instruction illegal in U Mode.

  * ``cp_mret_in_umode`` - ``MRET``
  * ``cp_wfi_in_umode`` - ``WFI``
  * Read and write to M-mode CSR - Covered by crosses ``csr_write_priv_cross`` and ``csr_read_only_priv_cross```

* Debug mode instructions (cover execution in and out of debug mode).

  * ``DRET``
  * ``csr_read_only_debug_cross``, ``csr_write_debug_cross`` - Access to debug CSRs.

    * ``dcsr``
    * ``dpc``
    * ``dscratch0``
    * ``dscratch1``

  * Access to trigger CSRs (also possible in M mode: cover execution in M mode, debug mode and U mode).
    Covered by ``csr_read_only_debug_cross``, ``csr_write_debug_cross``, ``csr_read_only_priv_cross``, ``csr_write_priv_cross``.

    * ``tselect``
    * ``tdata1``
    * ``tdata2``
    * ``tdata3``

* Loads/stores with ``mstatus.mprv`` set and unset.
* EBreak behaviour in U/M mode with different ``dcsr.ebreakm`` / ``dcsr.ebreaku`` settings.
  Covered by ``priv_mode_instr_cross``

Pipeline State
^^^^^^^^^^^^^^
Each pipeline stage has some associated state.

* ``cp_if_stage_state`` - IF stage full and fetching, full and idle, empty and fetching, or empty and idle.
  General IF stage full and stalled uninteresting as will only occur when ID stage is full and stalled.
* ``cp_wb_stage_state`` - WB stage full and stalled, full and unstalled, or empty
* ``cp_id_stage_state`` - ID stage full and stalled, full and unstalled, or empty.
* Controller (within ID stage) state machine states

  * ``cp_controller_fsm`` - Possible transitions between these states.
    Those marked with a '*' are of particular interest and should be crossed with instruction categories and other coverpoints as appropriate to fully explore the transitions.

    * ``RESET`` -> ``BOOT_SET``
    * ``BOOT_SET`` -> ``FIRST_FETCH``
    * ``FIRST_FETCH`` -> ``DECODE``
    * ``FIRST_FETCH`` -> ``IRQ_TAKEN``
    * ``FIRST_FETCH`` -> ``DBG_TAKEN_IF``
    * ``DECODE`` -> ``FLUSH`` *
    * ``DECODE`` -> ``DBG_TAKEN_IF`` *
    * ``DECODE`` -> ``IRQ_TAKEN`` *
    * ``IRQ_TAKEN`` -> ``DECODE``
    * ``DBG_TAKEN_IF`` -> ``DECODE``
    * ``DBG_TAKEN_ID`` -> ``DECODE``
    * ``FLUSH`` -> ``DECODE`` *
    * ``FLUSH`` -> ``DBG_TAKEN_ID``
    * ``FLUSH`` -> ``WAIT_SLEEP``
    * ``FLUSH`` -> ``IRQ_TAKEN`` *
    * ``FLUSH`` -> ``DBG_TAKEN_IF`` *
    * ``WAIT_SLEEP`` -> ``SLEEP``
    * ``SLEEP`` -> ``FIRST_FETCH``

Exceptions/Interrupts/Debug
^^^^^^^^^^^^^^^^^^^^^^^^^^^
Exceptions, interrupts and debug entry can all cause control flow changes combined with CSR writes and privilege level changes and work quite similarly within the controller but not identically.
Furthermore they can all occur together and must be appropriately prioritised (consider a instruction with hardware trigger point matching it, that causes some exception and an interrupt is raised the cycle it enters the ID/EX stage)

* Exception from instruction fetch error (covered by the **FetchError** instruction category).
* Exception from instruction PMP violation.
* Exception from illegal instruction (covered by the illegal instruction categories).
* Exception from memory fetch error.
* Exception from memory access PMP violation.
* Unaligned access cases (both accesses saw error, first or second only saw error, or neither saw error) for both kinds of memory exceptions.
* Interrupt raised/taken.

  * Interrupt raised/taken for each available interrupt line.
    For cross coverage, the precise interrupt that's raised/taken is not relevant and it only needs to be grouped by NMI vs non-NMI.
  * Interrupt raised/taken the first cycle an instruction is in ID/EX or some other cycle the instruction is in ID/EX.

* External debug request.
* Instruction executed when debug single step enabled.
* Instruction matches hardware trigger point.

  * Instruction matching trigger point causes exception

* Ibex operating in debug mode.
* Debug and Interrupt whilst sleeping with WFI

  * Cover with global interrupts enabled and disabled
  * Cover with specific interrupt enabled and disabled (Should exit sleep when
    interrupt is enabled but global interrupts set to disabled, should continue
    sleeping when both are disabled).

* Debug and interrupt occurring whilst entering WFI

  * Covering period between WFI entering ID/EX stage and going into sleep

* Double fault

PMP
^^^
* ``cp_region_mode`` - Each region configured with different matching modes.

  * Off
  * TOR
  * NA4
  * NAPOT

* ``cp_region_priv_bits`` - Each region configured with all possible permissions including locked/unlocked.

  * Different permissions with MML enabled and disabled, separate cover points for R/W/X/L values with and without MML.

* Access fail & pass.

  * All combinations of unaligned access split across a boundary, both halves pass, neither pass, just the first passes, just the second passes.

    * Two possible boundary splits; across a 32-bit boundary within a region or a boundary between PMP regions.

  * ``cp_pmp_iside_region_override``, ``cp_pmp_iside2_region_override``, ``cp_pmp_dside_region_override`` - Higher priority entry allows access that lower priority entry prevents.
  * Compressed instruction access (16-bit) passes PMP but 32-bit access at same address crosses PMP region boundary.

* Each field of mssecfg enabled/disabled with relevant functionality tested.

  * RLB - rule locking bypass.

    * Modify locked region with RLB set.
    * Try to enable RLB when RLB is disabled and locked regions present.

  * MMWP - machine mode whitelist policy.

    * M-mode access fail due to not matching any PMP regions.
    * Try to disable when enabled.

  * MML - machine mode lockdown policy.

    * Try to disable when enabled.

* Access close to PMP region modification that allows/disallows that access.

CSRs
^^^^
Basic read/write functionality must be tested on all implemented CSRs.

* ``cp_csr_read_only`` - Read from CSR.
* ``cp_csr_write`` -  Write to CSR.

  * Write to read only CSR.
    Covered by ensuring ``cp_csr_write`` is seen for read-only CSRs

* Write illegal/unsupported value to WARL field.
* ``csr_read_only_priv_cross``, ``csr_write_priv_cross``, ``csr_read_only_debug_cross``, ``csr_write_debug_cross`` - Crosses of reads and writes to CSRs from different privilege levels/debug mode.

  * Access to CSR disallowed due to privilege levels/debug mode
    Covered by ensuring within the crosses

* Read and write from/to an unimplemented CSR

CSRs addresses do not need to be crossed with the variety of CSR instructions as these all use the same basic read & write interface into ``ibex_cs_registers``.
Coverage of the above points will be sampled at the ``ibex_cs_registers`` interface (as opposed to sampling CSR instructions).

Miscellaneous
^^^^^^^^^^^^^
Various points of interest do not fit into the categories above.

* ``instr_unstalled`` - Instruction unstalled - Cover the cycle an instruction is unstalled having just been stalled.
* Enabling/Disabling ICache.

Cross Coverage
--------------
Much of the more complex behaviour lies at the combination of the individual microarchitectural behaviours above.
Cross coverage is used to capture that.
Crosses listed below are ones that don't already fit into the above categories.
There are some broad crosses containing many bins aiming to capture all combinations of some generalised behaviours as well as some more specific ones to capture all combinations of behaviours focused on a particular area.

Cross coverage will be intentionally broad.
Where it is proving hard to hit particular bins they will be reviewed in more detail to determine if they're impossible to hit or if simply hard to hit and whether hitting them provides meaningful gains to verification quality.

Excluded bins will either become illegal bins (where they are impossible to hit, so a failure will be seen if they are hit) or ignore bins (where they don't factor into coverage statistics).
There must be a documented reason a particular bin is added to the illegal or ignore bins.

* ``pipe_cross`` - Instruction Categories x Pipeline stage states across IF, ID/EX and WB

  * Covers all possibilities of instruction combinations that could fill the pipeline. State only for IF/WB suffices to cover this as all the interesting per instruction behaviour occurs in ID/EX.
  * All bins containing instruction categories other than **None** ignored when ID/EX stage is empty.

* ``priv_mode_instr_cross`` - Instructions Categories x ID/EX Privilege level
* ``stall_cross`` - Instruction Categories x Stall Categories

  * Illegal bins will be used to exclude instruction and stall categories that cannot occur.

* ``wb_reg_no_load_hz_instr_cross`` - Instruction Categories x Hazards

  * ``stall_cross`` covers the RAW load hazard (as it produces a LdHz stall).
  * RAW hazard between load/store requires no cross coverage as it's only seen for load and store instructions so the single coverpoint suffices.

* ``debug_instruction_cross`` - Instruction Categories x Debug Mode
* Instruction Categories x Controller state transitions of interest
* ``interrupt_taken_instr_cross``, ``debug_entry_if_instr_cross``, ``pipe_flush_instr_cross`` - Interrupt taken/Debug mode entry/Pipe flush x instruction unstalled x instruction category

  * Three separate cross coverage groups: one for interrupt, debug and pipe flush.
  * Covers all instruction categories being interrupted/entering debug mode/flushing the pipeline both where this occurs during a stall and when it occurs just when they've unstalled.

* ``exception_stall_instr_cross`` - PMP exception x load/store error exception x instruction category x stall type x unstalled x irq pending x debug req

  * Large cross to cover all possibilities of combinations between interrupt, debug and exceptions for all instruction categories across all stall behaviours.

* ``pmp_iside_priv_bits_cross``, ``pmp_iside2_priv_bits_cross``, ``pmp_dside_priv_bits_cross``, PMP regions x permissions x access fail/pass x privilege level

  * Three crosses, one for each PMP channel (instruction, instruction 2 and data).
