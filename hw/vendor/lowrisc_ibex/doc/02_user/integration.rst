.. _core-integration:

Core Integration
================

The main module is named ``ibex_top`` and can be found in ``ibex_top.sv``.
Note that the core logic is split-out from the register file and RAMs under ``ibex_top``.
This is to facilitate a dual-core lockstep implementation (see :ref:`security`).

Register File
-------------

Ibex comes with three different register file implementations that can be selected using the enumerated parameter ``RegFile`` defined in :file:`rtl/ibex_pkg.sv`.
Depending on the target technology, either the flip-flop-based ("ibex_pkg::RegFileFF", default), the latch-based ("ibex_pkg::RegFileLatch") or an FPGA-targeted ("ibex_pkg::RegFileFPGA") implementation should be selected.
For more information about the three register file implementations and their trade-offs, check out :ref:`register-file`.

Identification CSRs
-------------------

The RISC-V Privileged Architecture specifies several read-only CSRs that identify the vendor and micro-architecture of a CPU.
These are ``mvendorid``, ``marchid`` and ``mimpid``.
Implementers should carefully consider appropriate values for these registers.
Ibex, as an open source implementation, has an assigned architecture ID (``marchid``) of 22.
(Allocations are specified in `marchid.md of the riscv-isa-manual repository <https://github.com/riscv/riscv-isa-manual/blob/master/marchid.md>`_.)
If significant changes are made to the micro-architecture a different architecture ID should be used.
The vendor ID and implementation ID (``mvendorid`` and ``mimpid``) are configurable via the ``CsrMvendorId`` and ``CsrMimpId`` top-level parameters and default to 0 (non-implemented).
Implementers may wish to use other values here.
Please see the RISC-V Privileged Architecture specification for more details on what these IDs represent and how they should be chosen.

.. _integration-prims:

Primitives
----------

Ibex uses a number of primitive modules (that are held outside the :file:`rtl/` which contains the Ibex RTL).
Full implementations of these primitives are provided in the Ibex repository but implementers may wish to provide their own implementations.
Some of the primitives are only used for specific Ibex configurations so can be ignored/removed if you're not using one of those configurations.

The mandatory primitives (used by all configurations) are:
 * ``prim_buf`` - A buffer, used to ensure security critical logic isn't optimized out in synthesis (by applying suitable constraints to prim_buf).
   In configurations where ``SecureIbex == 0`` it must exist but can be implemented as a straight passthrough.
 * ``prim_clock_gating`` - A clock gate.

The configuration dependent primitives are:
 * ``prim_clock_mux2`` - A clock mux, used by the lockstep duplicate core.
   Required where ``SecureIbex == 1``.
 * ``prim_flop`` - A flip flop, used to ensure security critical logic isn't optimized out in synthesis (by applying suitable constraints to prim_flop).
   Required where ``SecureIbex == 1``.
 * ``prim_ram_1p`` - A single ported RAM.
   Required where ``ICache == 1``.
 * ``prim_ram_1p_scr`` - A single ported RAM which scrambles its contents with cryptographic primitives.
   Required where ``ICache == 1`` and ``SecureIbex == 1``.
 * ``prim_lfsr`` - Linear feedback shift register, used for pseudo random number generation for dummy instruction insertion.
   Required where ``SecureIbex == 1``.
 * ``prim_secded_X`` - Various primitives to encode and decode SECDED (Single Error Correct, Double Error Detect) error detection and correction codes.
   Required where ``SecureIbex == 1``.

Primitives exclusively used by other primitives:
 * ``prim_present`` / ``prim_prince`` / ``prim_subst_perm`` - Cryptographic primitives used by ``prim_ram_1p_scr``.
 * ``prim_ram_1p_adv`` - Wrapper around ``prim_ram_1p`` that adds support for ECC, used by ``prim_ram_1p_scr``.

.. _integration-fusesoc-files:

RTL File List
-------------

Ibex flows use `FuseSoC <https://github.com/olofk/fusesoc>`_ to gather needed RTL files and run builds.
If you want to use Ibex without FuseSoC the following FuseSoC command will copy all the needed files into a build directory.

.. code-block:: bash

  fusesoc --cores-root . run --target=lint --setup --build-root ./build/ibex_out lowrisc:ibex:ibex_top

FuseSoC uses Python and it can be installed using pip.

.. code-block:: bash

  pip3 install -U -r python-requirements.txt

The RTL will be in :file:`./build/ibex_out/src` which is further divided into different sub-directories.
A file list containing paths to all of the RTL files can be found in :file:`./build/ibex_out/ibex-verilator/lowrisc_ibex_ibex_top_0.1.vc`.

Instantiation Template
----------------------

.. code-block:: verilog

  ibex_top #(
      .BaseIsa                      ( ibex_pkg::BaseIsaRV32I           ),
      .PMPEnable                    ( 1'b0                             ),
      .PMPGranularity               ( 0                                ),
      .PMPNumRegions                ( 4                                ),
      .MHPMCounterNum               ( 0                                ),
      .MHPMCounterWidth             ( 40                               ),
      .PMPRstCfg                    ( ibex_pkg::PmpCfgRst              ),
      .PMPRstAddr                   ( ibex_pkg::PmpAddrRst             ),
      .PMPRstMsecCfg                ( ibex_pkg::PmpMseccfgRst          ),
      .CheriotRevBitmapAddrWidth    ( 32'd11                           ),
      .CheriotRevBitmapBaseAddr     ( 32'h0                            ),
      .RV32E                        ( 1'b0                             ),
      .RV32M                        ( ibex_pkg::RV32MFast              ),
      .RV32B                        ( ibex_pkg::RV32BNone              ),
      .RV32ZC                       ( ibex_pkg::RV32ZcaZcbZcmp         ),
      .RegFile                      ( ibex_pkg::RegFileFF              ),
      .BranchTargetALU              ( 1'b0                             ),
      .WritebackStage               ( 1'b0                             ),
      .ICache                       ( 1'b0                             ),
      .ICacheECC                    ( 1'b0                             ),
      .BranchPredictor              ( 1'b0                             ),
      .DbgTriggerEn                 ( 1'b0                             ),
      .DbgHwBreakNum                ( 1                                ),
      .SecureIbex                   ( 1'b0                             ),
      .LockstepOffset               ( 1                                ),
      .MemECC                       ( 1'b0                             ),
      .MemDataWidth                 ( 32                               ),
      .ICacheScramble               ( 1'b0                             ),
      .ICacheScrNumPrinceRoundsHalf ( 2                                ),
      .ICacheTweakInfection         ( 1'b0                             ),
      .RndCnstLfsrSeed              ( ibex_pkg::RndCnstLfsrSeedDefault ),
      .RndCnstLfsrPerm              ( ibex_pkg::RndCnstLfsrPermDefault ),
      .DmBaseAddr                   ( 32'h1A110000                     ),
      .DmAddrMask                   ( 32'h00000FFF                     ),
      .DmHaltAddr                   ( 32'h1A110800                     ),
      .DmExceptionAddr              ( 32'h1A110808                     ),
      .RndCnstIbexKey               ( ibex_pkg::RndCnstIbexKeyDefault  ),
      .RndCnstIbexNonce             ( ibex_pkg::RndCnstIbexNonceDefault),
      .CsrMvendorId                 ( 32'b0                            ),
      .CsrMimpId                    ( 32'b0                            )
  ) u_top (
      // Clock and Reset
      .clk_i                        ( ),
      .rst_ni                       ( ),

      .test_en_i                    ( ),
      .ram_cfg_icache_tag_i         ( ),
      .ram_cfg_icache_tag_o         ( ),
      .ram_cfg_icache_data_i        ( ),
      .ram_cfg_icache_data_o        ( ),

      // CHERIoT configuration
      .cheriot_enable_i             ( ),
      .hart_id_i                    ( ),
      .boot_addr_i                  ( ),
      .trvk_heap_base_addr_i        ( ),

      // Instruction memory interface
      .instr_req_o                  ( ),
      .instr_gnt_i                  ( ),
      .instr_rvalid_i               ( ),
      .instr_addr_o                 ( ),
      .instr_rdata_i                ( ),
      .instr_rdata_intg_i           ( ),
      .instr_err_i                  ( ),

      // Data memory interface
      .data_req_o                   ( ),
      .data_gnt_i                   ( ),
      .data_rvalid_i                ( ),
      .data_we_o                    ( ),
      .data_be_o                    ( ),
      .data_addr_o                  ( ),
      .data_wdata_o                 ( ),
      .data_wdata_intg_o            ( ),
      .data_tag_o                   ( ),
      .data_rdata_i                 ( ),
      .data_rdata_intg_i            ( ),
      .data_tag_i                   ( ),
      .data_err_i                   ( ),

      // TRVK revocation bitmap read interface
      .trvk_revbm_req_o             ( ),
      .trvk_revbm_gnt_i             ( ),
      .trvk_revbm_rvalid_i          ( ),
      .trvk_revbm_addr_o            ( ),
      .trvk_revbm_rdata_i           ( ),
      .trvk_revbm_rdata_intg_i      ( ),
      .trvk_revbm_err_i             ( ),

      // Interrupt inputs
      .irq_software_i               ( ),
      .irq_timer_i                  ( ),
      .irq_external_i               ( ),
      .irq_fast_i                   ( ),
      .irq_nm_i                     ( ),

      // Scrambling Interface
      .scramble_key_valid_i         ( ),
      .scramble_key_i               ( ),
      .scramble_nonce_i             ( ),
      .scramble_req_o               ( ),

      // Debug Interface
      .debug_req_i                  ( ),
      .crash_dump_o                 ( ),
      .double_fault_seen_o          ( ),

      // CPU Control Signals
      .fetch_enable_i               ( ),
      .mcounteren_writable_i        ( ),
      .alert_minor_o                ( ),
      .alert_major_internal_o       ( ),
      .alert_major_bus_o            ( ),
      .core_sleep_o                 ( ),

      // DFT bypass controls
      .scan_rst_ni                  ( ),

      // Lockstep signals
      .lockstep_cmp_en_o            ( ),

      // Shadow core data interface outputs
      .data_req_shadow_o            ( ),
      .data_we_shadow_o             ( ),
      .data_be_shadow_o             ( ),
      .data_addr_shadow_o           ( ),
      .data_wdata_shadow_o          ( ),
      .data_wdata_intg_shadow_o     ( ),

      // Shadow core instruction interface outputs
      .instr_req_shadow_o           ( ),
      .instr_addr_shadow_o          ( )

  `ifdef RVFI
      // RISC-V Formal Interface
      ,.rvfi_valid                  ( ),
      .rvfi_order                   ( ),
      .rvfi_insn                    ( ),
      .rvfi_trap                    ( ),
      .rvfi_halt                    ( ),
      .rvfi_intr                    ( ),
      .rvfi_mode                    ( ),
      .rvfi_ixl                     ( ),
      .rvfi_rs1_addr                ( ),
      .rvfi_rs2_addr                ( ),
      .rvfi_rs3_addr                ( ),
      .rvfi_rs1_rdata               ( ),
      .rvfi_rs2_rdata               ( ),
      .rvfi_rs3_rdata               ( ),
      .rvfi_rs1_rcap                ( ),
      .rvfi_rs2_rcap                ( ),
      .rvfi_rd_wcap                 ( ),
      .rvfi_rd_addr                 ( ),
      .rvfi_rd_wdata                ( ),
      .rvfi_pc_rdata                ( ),
      .rvfi_pc_wdata                ( ),
      .rvfi_mem_addr                ( ),
      .rvfi_mem_rmask               ( ),
      .rvfi_mem_wmask               ( ),
      .rvfi_mem_rdata               ( ),
      .rvfi_mem_wdata               ( ),
      .rvfi_mem_is_cap              ( ),
      .rvfi_mem_rcap                ( ),
      .rvfi_mem_wcap                ( ),
      .rvfi_ext_pre_mip             ( ),
      .rvfi_ext_post_mip            ( ),
      .rvfi_ext_nmi                 ( ),
      .rvfi_ext_nmi_int             ( ),
      .rvfi_ext_debug_req           ( ),
      .rvfi_ext_debug_mode          ( ),
      .rvfi_ext_rf_wr_suppress      ( ),
      .rvfi_ext_mcycle              ( ),
      .rvfi_ext_mhpmcounters        ( ),
      .rvfi_ext_mhpmcountersh       ( ),
      .rvfi_ext_ic_scr_key_valid    ( ),
      .rvfi_ext_irq_valid           ( ),
      .rvfi_ext_expanded_insn_valid ( ),
      .rvfi_ext_expanded_insn       ( ),
      .rvfi_ext_expanded_insn_last  ( )
  `endif
  );

.. _parameters:

Parameters
----------

+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| Name                             | Type/Range          | Default                 | Description                                                                                  |
+==================================+=====================+=========================+==============================================================================================+
| ``BaseIsa``                      | base_isa_e          | BaseIsaRV32I            | Selects the base ISA mode:                                                                   |
|                                  |                     |                         |  - ``ibex_pkg::BaseIsaRV32I``: RV32I only                                                    |
|                                  |                     |                         |  - ``ibex_pkg::BaseIsaRV32IorCHERIoT``: runtime-switchable RV32I/CHERIoT (:ref:`cheriot`)    |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``PMPEnable``                    | bit                 | 0                       | Enable :ref:`pmp`                                                                            |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``PMPGranularity``               | int (0..31)         | 0                       | Minimum granularity of PMP address matching                                                  |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``PMPNumRegions``                | int (1..16)         | 4                       | Number implemented PMP regions (ignored if PMPEnable == 0)                                   |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``MHPMCounterNum``               | int (0..10)         | 0                       | Number of :ref:`performance-counters`                                                        |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``MHPMCounterWidth``             | int (1..64)         | 40                      | Bit width of performance monitor event counters                                              |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``PMPRstCfg``                    | pmp_cfg_t[]         | PmpCfgRst               | Reset values for PMP configuration registers                                                 |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``PMPRstAddr``                   | logic[]             | PmpAddrRst              | Reset values for PMP address registers                                                       |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``PMPRstMsecCfg``                | pmp_mseccfg_t       | PmpMseccfgRst           | Reset value for the ``mseccfg`` register (:ref:`pmp-enhancements`)                           |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``CheriotRevBitmapAddrWidth``    | int unsigned        | 11                      | Log2 of the revocation bitmap memory size in bytes. Only relevant                            |
|                                  |                     |                         | when ``BaseIsa == BaseIsaRV32IorCHERIoT``. See :ref:`cheriot`.                               |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``CheriotRevBitmapBaseAddr``     | int unsigned        | 0x0                     | Base byte address of the revocation bitmap memory. Only relevant                             |
|                                  |                     |                         | when ``BaseIsa == BaseIsaRV32IorCHERIoT``. See :ref:`cheriot`.                               |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``RV32E``                        | bit                 | 0                       | RV32E mode enable (16 integer registers only)                                                |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``RV32M``                        | ibex_pkg::rv32m_e   | RV32MFast               | M(ultiply) extension select (see :ref:`mult-div`):                                           |
|                                  |                     |                         |  - "ibex_pkg::RV32MNone": No M-extension                                                     |
|                                  |                     |                         |  - "ibex_pkg::RV32MSlow": Slow multi-cycle multiplier, iterative divider                     |
|                                  |                     |                         |  - "ibex_pkg::RV32MFast": 3-4 cycle multiplier, iterative divider                            |
|                                  |                     |                         |  - "ibex_pkg::RV32MSingleCycle": 1-2 cycle multiplier, iterative divider                     |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``RV32B``                        | ibex_pkg::rv32b_e   | RV32BNone               | B(itmanipulation) extension select:                                                          |
|                                  |                     |                         |  - "ibex_pkg::RV32BNone": No B-extension                                                     |
|                                  |                     |                         |  - "ibex_pkg::RV32BBalanced": Sub-extensions Zba, Zbb, Zbs                                   |
|                                  |                     |                         |  - "ibex_pkg::RV32BFull": Balanced plus Zbc, Zbkb, Zbkx                                      |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``RV32ZC``                       | ibex_pkg::rv32zc_e  | RV32ZcaZcbZcmp          | Zc code-size saving extension select:                                                        |
|                                  |                     |                         |  - "ibex_pkg::RV32Zca": The Zca extension                                                    |
|                                  |                     |                         |  - "ibex_pkg::RV32ZcaZcb": Zca and Zcb extensions                                            |
|                                  |                     |                         |  - "ibex_pkg::RV32ZcaZcmp": Zca and Zcmp extensions                                          |
|                                  |                     |                         |  - "ibex_pkg::RV32ZcaZcbZcmp": Zca, Zcb, and Zcmp extensions                                 |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``RegFile``                      | ibex_pkg::regfile_e | RegFileFF               | :ref:`register-file` implementation select:                                                  |
|                                  |                     |                         |  - "ibex_pkg::RegFileFF": Generic flip-flop-based register file                              |
|                                  |                     |                         |  - "ibex_pkg::RegFileFPGA": Register file for FPGA targets                                   |
|                                  |                     |                         |  - "ibex_pkg::RegFileLatch": Latch-based register file for ASIC targets                      |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``BranchTargetALU``              | bit                 | 0                       | Enables branch target ALU removing a stall cycle from taken branches                         |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``WritebackStage``               | bit                 | 0                       | Enables third pipeline stage (writeback) improving performance of                            |
|                                  |                     |                         | loads and stores (:ref:`pipeline-details`)                                                   |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``ICache``                       | bit                 | 0                       | Enable :ref:`icache` instead of prefetch buffer                                              |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``ICacheECC``                    | bit                 | 0                       | Enable :ref:`icache-ecc` (if ICache == 1)                                                    |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``BranchPredictor``              | bit                 | 0                       | *EXPERIMENTAL* Enable :ref:`branch-prediction`                                               |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``DbgTriggerEn``                 | bit                 | 0                       | Enable :ref:`debug-support` triggers (``DbgHwBreakNum`` for count)                           |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``DbgHwBreakNum``                | int (>= 1)          | 1                       | Number of hardware breakpoints (debug triggers) supported                                    |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``SecureIbex``                   | bit                 | 0                       | Enable various :ref:`security`. Note: SecureIbex == 1'b1 and                                 |
|                                  |                     |                         | RV32M == ibex_pkg::RV32MNone is an illegal combination.                                      |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``LockstepOffset``               | int (>= 1)          | 1                       | Number of cycles to delay the :ref:`lockstep` shadow core                                    |
|                                  |                     |                         | (only relevant when SecureIbex == 1'b1)                                                      |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``MemECC``                       | bit                 | SecureIbex              | Enable SECDED ECC for :ref:`bus-integrity`                                                   |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``MemDataWidth``                 | 32 or 39            | MemECC ? 32 + 7 : 32    | Data width of memory interface including integrity bits                                      |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``ICacheScramble``               | bit                 | 0                       | Replace ICache tag/data RAMs with                                                            |
|                                  |                     |                         | :ref:`scrambling RAM <icache-scramble-key>` primitives                                       |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``ICacheScrNumPrinceRoundsHalf`` | int (1..5)          | 2                       | Number of PRINCE half-rounds used for ICache data scrambling                                 |
|                                  |                     |                         | (only relevant when ICacheScramble == 1)                                                     |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``ICacheTweakInfection``         | bit                 | SecureIbex              | Enable :ref:`icache-tweak-infection`                                                         |
|                                  |                     |                         | (only relevant when ICache == 1 and ICacheECC == 1)                                          |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``RndCnstLfsrSeed``              | lfsr_seed_t         | RndCnstLfsrSeedDefault  | LFSR seed for :ref:`dummy-instruction-insertion`                                             |
|                                  |                     |                         | (only relevant when SecureIbex == 1'b1)                                                      |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``RndCnstLfsrPerm``              | lfsr_perm_t         | RndCnstLfsrPermDefault  | Set the permutation applied to the output of the LFSR used to                                |
|                                  |                     |                         | generate dummy instructions (only relevant when SecureIbex == 1'b1)                          |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``DmBaseAddr``                   | int                 | 0x1A110000              | Base address of the Debug Module                                                             |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``DmAddrMask``                   | int                 | 0x00000FFF              | Address mask of the Debug Module                                                             |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``DmHaltAddr``                   | int                 | 0x1A110800              | Address to jump to when entering Debug Mode                                                  |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``DmExceptionAddr``              | int                 | 0x1A110808              | Address to jump to when an exception occurs while in Debug Mode                              |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``RndCnstIbexKey``               | logic[]             | RndCnstIbexKeyDefault   | Reset value of the ICache scrambling key (only relevant when ICacheScramble == 1)            |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``RndCnstIbexNonce``             | logic[]             | RndCnstIbexNonceDefault | Reset value of the ICache scrambling nonce (only relevant when ICacheScramble == 1)          |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``CsrMvendorId``                 | logic [31:0]        | 32'b0                   | Value of the ``mvendorid`` CSR. See :ref:`cs-registers` and                                  |
|                                  |                     |                         | :ref:`core-integration` for details.                                                         |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+
| ``CsrMimpId``                    | logic [31:0]        | 32'b0                   | Value of the ``mimpid`` CSR. See :ref:`cs-registers` and                                     |
|                                  |                     |                         | :ref:`core-integration` for details.                                                         |
+----------------------------------+---------------------+-------------------------+----------------------------------------------------------------------------------------------+

Any parameter marked *EXPERIMENTAL* when enabled is not verified to the same standard as the rest of the Ibex core.

Note that Ibex uses SystemVerilog enum parameters e.g. for ``RV32M`` and ``RV32B``.
This is well supported by most tools but some care is needed when overriding these parameters at the top level:

* Synopsys VCS does not support overriding enum and string parameters at the top level via command line.
  As a workaround, SystemVerilog defines are used in Ibex top level files simulated with VCS.
  These defines can be set via command line.

* Yosys does not support overriding enum parameters at the top level by setting enum names.
  Instead, the enum values need to be used.

Interfaces
----------

+------------------------------+-------------------------+-----+----------------------------------------+
| Signal(s)                    | Width                   | Dir | Description                            |
+==============================+=========================+=====+========================================+
| ``clk_i``                    | 1                       | in  | Clock signal                           |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``rst_ni``                   | 1                       | in  | Active-low asynchronous reset          |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``test_en_i``                | 1                       | in  | Test input, enables clock and allows   |
|                              |                         |     | test control of reset.                 |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``scan_rst_ni``              | 1                       | in  | Test controlled reset. If DFT not      |
|                              |                         |     | used, tie off to 1.                    |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``ram_cfg_icache_tag_i``     | ram_1p_cfg_req_t        | in  | Per-way icache tag RAM config input,   |
|                              |                         |     | routed to the icache tag RAMs          |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``ram_cfg_icache_tag_o``     | ram_1p_cfg_rsp_t        | out | Per-way icache tag RAM config          |
|                              |                         |     | response from the icache tag RAMs      |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``ram_cfg_icache_data_i``    | ram_1p_cfg_req_t        | in  | Per-way icache data RAM config input,  |
|                              |                         |     | routed to the icache data RAMs         |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``ram_cfg_icache_data_o``    | ram_1p_cfg_rsp_t        | out | Per-way icache data RAM config         |
|                              |                         |     | response from the icache data RAMs     |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``cheriot_enable_i``         | ibex_mubi_t             | in  | Runtime enable for CHERIoT mode.       |
|                              |                         |     | ``IbexMuBiOn`` enables CHERIoT         |
|                              |                         |     | instructions and capability registers. |
|                              |                         |     | Only active when                       |
|                              |                         |     | ``BaseIsa == BaseIsaRV32IorCHERIoT``.  |
|                              |                         |     | Tie to ``IbexMuBiOff`` to always run   |
|                              |                         |     | in RV32I mode.                         |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``hart_id_i``                | 32                      | in  | Hart ID, usually static, can be read   |
|                              |                         |     | from :ref:`csr-mhartid` CSR            |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``boot_addr_i``              | 32                      | in  | First program counter after reset      |
|                              |                         |     | = ``boot_addr_i`` + 0x80,              |
|                              |                         |     | see :ref:`exceptions-interrupts`       |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``trvk_heap_base_addr_i``    | 32                      | in  | Base address of the heap region for    |
|                              |                         |     | CHERIoT capability revocation. Used    |
|                              |                         |     | by the TRVK filter to determine which  |
|                              |                         |     | load results need revocation checking. |
|                              |                         |     | See :ref:`cheriot`.                    |
|                              |                         |     | Tie to 0 in non-CHERIoT mode.          |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``instr_*``                  | Instruction fetch interface, see :ref:`instruction-fetch`              |
+------------------------------+------------------------------------------------------------------------+
| ``data_*``                   | Load-store unit interface, see :ref:`load-store-unit`                  |
+------------------------------+------------------------------------------------------------------------+
| ``trvk_revbm_*``             | :ref:`cheriot` revocation bitmap read interface.                       |
|                              | Used by the TRVK filter to check whether a loaded capability           |
|                              | has been revoked. If ``BaseIsa == BaseIsaRV32I`` this interface        |
|                              | can be tied off.                                                       |
+------------------------------+------------------------------------------------------------------------+
| ``irq_*``                    | Interrupt inputs, see :ref:`exceptions-interrupts`                     |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``scramble_*``               | Scrambling key interface, see :ref:`icache`                            |
+------------------------------+------------------------------------------------------------------------+
| ``debug_*``                  | Debug interface, see :ref:`debug-support`                              |
+------------------------------+------------------------------------------------------------------------+
| ``crash_dump_o``             | A set of signals that can be captured on reset to aid crash debugging. |
|                              | The ``current_pc`` and ``next_pc`` fields are only guaranteed to be    |
|                              | defined after reset if ``SecureIbex`` and thereby ``ResetAll`` is      |
|                              | enabled.                                                               |
+------------------------------+------------------------------------------------------------------------+
| ``double_fault_seen_o``      | A double fault was observed, see :ref:`double-fault-detect`            |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``fetch_enable_i``           | ibex_mubi_t             | in  | Allow the core to fetch instructions.  |
|                              |                         |     | If not set to IbexMuBiOn, the core     |
|                              |                         |     | will pause fetching new instructions   |
|                              |                         |     | immediately halt once any in-flight    |
|                              |                         |     | instructions in the ID/EX and WB       |
|                              |                         |     | stages have finished. A multi-bit      |
|                              |                         |     | encoding scheme is used. See           |
|                              |                         |     | `IbexMuBiOn` / `IbexMuBiOff` in        |
|                              |                         |     | :file:`rtl/ibex_pkg.sv`                |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``core_sleep_o``             | 1                       | out | Core in WFI with no outstanding data   |
|                              |                         |     | or instruction accesses. Deasserts     |
|                              |                         |     | if an external event (interrupt or     |
|                              |                         |     | debug req) wakes the core up           |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``alert_minor_o``            | 1                       | out | Core has detected a fault which it can |
|                              |                         |     | safely recover from. Can be used by a  |
|                              |                         |     | system to log errors over time and     |
|                              |                         |     | detect tampering / attack. This signal |
|                              |                         |     | is a pulse, one cycle per alert.       |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``alert_major_internal_o``   | 1                       | out | Core has detected an internal fault    |
|                              |                         |     | which cannot be recovered from. Can be |
|                              |                         |     | used by a system to reset the core and |
|                              |                         |     | possibly  take other remedial action.  |
|                              |                         |     | This signal is a pulse, but might be   |
|                              |                         |     | set for multiple cycles per alert.     |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``alert_major_bus_o``        | 1                       | out | Core has detected a bus fault          |
|                              |                         |     | which cannot be recovered from. Can be |
|                              |                         |     | used by a system to reset the core and |
|                              |                         |     | possibly  take other remedial action.  |
|                              |                         |     | This signal is a pulse, but might be   |
|                              |                         |     | set for multiple cycles per alert.     |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``mcounteren_writable_i``    | ibex_mubi_t             | in  | When set to ``IbexMuBiOn``, the        |
|                              |                         |     | ``mcounteren`` CSR is writable.        |
|                              |                         |     | Uses the multi-bit encoding from       |
|                              |                         |     | :file:`rtl/ibex_pkg.sv`.               |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``lockstep_cmp_en_o``        | ibex_mubi_t             | out | Indicates that the lockstep shadow     |
|                              |                         |     | core comparison is active. Only        |
|                              |                         |     | relevant when ``SecureIbex == 1``.     |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``data_req_shadow_o``        | 1                       | out | Shadow core data outputs. These        |
+------------------------------+-------------------------+     | replicate the corresponding            |
| ``data_we_shadow_o``         | 1                       |     | ``data_*`` signals from the lockstep   |
+------------------------------+-------------------------+     | shadow core and can be used by an      |
| ``data_be_shadow_o``         | 4                       |     | external comparator to detect          |
+------------------------------+-------------------------+     | divergence. Only relevant when         |
| ``data_addr_shadow_o``       | 32                      |     | ``SecureIbex == 1``.                   |
+------------------------------+-------------------------+     |                                        |
| ``data_wdata_shadow_o``      | 32                      |     |                                        |
+------------------------------+-------------------------+     |                                        |
| ``data_wdata_intg_shadow_o`` | 7                       |     |                                        |
+------------------------------+-------------------------+     |                                        |
| ``instr_req_shadow_o``       | 1                       |     |                                        |
+------------------------------+-------------------------+     |                                        |
| ``instr_addr_shadow_o``      | 32                      |     |                                        |
+------------------------------+-------------------------+-----+----------------------------------------+
| ``rvfi_*``                   | conditional             | out | RISC-V Formal Interface signals        |
|                              |                         |     | present only when ``RVFI`` is defined. |
+------------------------------+-------------------------+-----+----------------------------------------+
