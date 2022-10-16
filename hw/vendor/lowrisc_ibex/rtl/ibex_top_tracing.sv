// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Top level module of the ibex RISC-V core with tracing enabled
 */

module ibex_top_tracing import ibex_pkg::*; #(
  parameter bit          PMPEnable        = 1'b0,
  parameter int unsigned PMPGranularity   = 0,
  parameter int unsigned PMPNumRegions    = 4,
  parameter int unsigned MHPMCounterNum   = 0,
  parameter int unsigned MHPMCounterWidth = 40,
  parameter bit          RV32E            = 1'b0,
  parameter rv32m_e      RV32M            = RV32MFast,
  parameter rv32b_e      RV32B            = RV32BNone,
  parameter regfile_e    RegFile          = RegFileFF,
  parameter bit          BranchTargetALU  = 1'b0,
  parameter bit          WritebackStage   = 1'b0,
  parameter bit          ICache           = 1'b0,
  parameter bit          ICacheECC        = 1'b0,
  parameter bit          BranchPredictor  = 1'b0,
  parameter bit          DbgTriggerEn     = 1'b0,
  parameter int unsigned DbgHwBreakNum    = 1,
  parameter bit          SecureIbex       = 1'b0,
  parameter bit          ICacheScramble   = 1'b0,
  parameter lfsr_seed_t  RndCnstLfsrSeed  = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t  RndCnstLfsrPerm  = RndCnstLfsrPermDefault,
  parameter int unsigned DmHaltAddr       = 32'h1A110800,
  parameter int unsigned DmExceptionAddr  = 32'h1A110808
) (
  // Clock and Reset
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic                         test_en_i,     // enable all clock gates for testing
  input  logic                         scan_rst_ni,
  input  prim_ram_1p_pkg::ram_1p_cfg_t ram_cfg_i,


  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,

  // Instruction memory interface
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  output logic [31:0]                  instr_addr_o,
  input  logic [31:0]                  instr_rdata_i,
  input  logic [6:0]                   instr_rdata_intg_i,
  input  logic                         instr_err_i,

  // Data memory interface
  output logic                         data_req_o,
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  output logic                         data_we_o,
  output logic [3:0]                   data_be_o,
  output logic [31:0]                  data_addr_o,
  output logic [31:0]                  data_wdata_o,
  output logic [6:0]                   data_wdata_intg_o,
  input  logic [31:0]                  data_rdata_i,
  input  logic [6:0]                   data_rdata_intg_i,
  input  logic                         data_err_i,

  // Interrupt inputs
  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i,
  input  logic                         irq_nm_i,       // non-maskeable interrupt

  // Scrambling Interface
  input  logic                         scramble_key_valid_i,
  input  logic [SCRAMBLE_KEY_W-1:0]    scramble_key_i,
  input  logic [SCRAMBLE_NONCE_W-1:0]  scramble_nonce_i,
  output logic                         scramble_req_o,

  // Debug Interface
  input  logic                         debug_req_i,
  output crash_dump_t                  crash_dump_o,
  output logic                         double_fault_seen_o,

  // CPU Control Signals
  input  fetch_enable_t                fetch_enable_i,
  output logic                         alert_minor_o,
  output logic                         alert_major_internal_o,
  output logic                         alert_major_bus_o,
  output logic                         core_sleep_o

);

  // ibex_tracer relies on the signals from the RISC-V Formal Interface
  `ifndef RVFI
    $fatal("Fatal error: RVFI needs to be defined globally.");
  `endif

  logic        rvfi_valid;
  logic [63:0] rvfi_order;
  logic [31:0] rvfi_insn;
  logic        rvfi_trap;
  logic        rvfi_halt;
  logic        rvfi_intr;
  logic [ 1:0] rvfi_mode;
  logic [ 1:0] rvfi_ixl;
  logic [ 4:0] rvfi_rs1_addr;
  logic [ 4:0] rvfi_rs2_addr;
  logic [ 4:0] rvfi_rs3_addr;
  logic [31:0] rvfi_rs1_rdata;
  logic [31:0] rvfi_rs2_rdata;
  logic [31:0] rvfi_rs3_rdata;
  logic [ 4:0] rvfi_rd_addr;
  logic [31:0] rvfi_rd_wdata;
  logic [31:0] rvfi_pc_rdata;
  logic [31:0] rvfi_pc_wdata;
  logic [31:0] rvfi_mem_addr;
  logic [ 3:0] rvfi_mem_rmask;
  logic [ 3:0] rvfi_mem_wmask;
  logic [31:0] rvfi_mem_rdata;
  logic [31:0] rvfi_mem_wdata;
  logic [31:0] rvfi_ext_mip;
  logic        rvfi_ext_nmi;
  logic        rvfi_ext_debug_req;
  logic [63:0] rvfi_ext_mcycle;

  logic [31:0] rvfi_ext_mhpmcounters [10];
  logic [31:0] rvfi_ext_mhpmcountersh [10];
  logic        rvfi_ext_ic_scr_key_valid;

  logic [31:0] unused_perf_regs [10];
  logic [31:0] unused_perf_regsh [10];


  logic [31:0] unused_rvfi_ext_mip;
  logic        unused_rvfi_ext_nmi;
  logic        unused_rvfi_ext_debug_req;
  logic [63:0] unused_rvfi_ext_mcycle;
  logic        unused_rvfi_ext_ic_scr_key_valid;

  // Tracer doesn't use these signals, though other modules may probe down into tracer to observe
  // them.
  assign unused_rvfi_ext_mip = rvfi_ext_mip;
  assign unused_rvfi_ext_nmi = rvfi_ext_nmi;
  assign unused_rvfi_ext_debug_req = rvfi_ext_debug_req;
  assign unused_rvfi_ext_mcycle = rvfi_ext_mcycle;
  assign unused_perf_regs = rvfi_ext_mhpmcounters;
  assign unused_perf_regsh = rvfi_ext_mhpmcountersh;
  assign unused_rvfi_ext_ic_scr_key_valid = rvfi_ext_ic_scr_key_valid;

  ibex_top #(
    .PMPEnable        ( PMPEnable        ),
    .PMPGranularity   ( PMPGranularity   ),
    .PMPNumRegions    ( PMPNumRegions    ),
    .MHPMCounterNum   ( MHPMCounterNum   ),
    .MHPMCounterWidth ( MHPMCounterWidth ),
    .RV32E            ( RV32E            ),
    .RV32M            ( RV32M            ),
    .RV32B            ( RV32B            ),
    .RegFile          ( RegFile          ),
    .BranchTargetALU  ( BranchTargetALU  ),
    .ICache           ( ICache           ),
    .ICacheECC        ( ICacheECC        ),
    .BranchPredictor  ( BranchPredictor  ),
    .DbgTriggerEn     ( DbgTriggerEn     ),
    .DbgHwBreakNum    ( DbgHwBreakNum    ),
    .WritebackStage   ( WritebackStage   ),
    .SecureIbex       ( SecureIbex       ),
    .ICacheScramble   ( ICacheScramble   ),
    .RndCnstLfsrSeed  ( RndCnstLfsrSeed  ),
    .RndCnstLfsrPerm  ( RndCnstLfsrPerm  ),
    .DmHaltAddr       ( DmHaltAddr       ),
    .DmExceptionAddr  ( DmExceptionAddr  )
  ) u_ibex_top (
    .clk_i,
    .rst_ni,

    .test_en_i,
    .scan_rst_ni,
    .ram_cfg_i,

    .hart_id_i,
    .boot_addr_i,

    .instr_req_o,
    .instr_gnt_i,
    .instr_rvalid_i,
    .instr_addr_o,
    .instr_rdata_i,
    .instr_rdata_intg_i,
    .instr_err_i,

    .data_req_o,
    .data_gnt_i,
    .data_rvalid_i,
    .data_we_o,
    .data_be_o,
    .data_addr_o,
    .data_wdata_o,
    .data_wdata_intg_o,
    .data_rdata_i,
    .data_rdata_intg_i,
    .data_err_i,

    .irq_software_i,
    .irq_timer_i,
    .irq_external_i,
    .irq_fast_i,
    .irq_nm_i,

    .scramble_key_valid_i,
    .scramble_key_i,
    .scramble_nonce_i,
    .scramble_req_o,

    .debug_req_i,
    .crash_dump_o,
    .double_fault_seen_o,

    .rvfi_valid,
    .rvfi_order,
    .rvfi_insn,
    .rvfi_trap,
    .rvfi_halt,
    .rvfi_intr,
    .rvfi_mode,
    .rvfi_ixl,
    .rvfi_rs1_addr,
    .rvfi_rs2_addr,
    .rvfi_rs3_addr,
    .rvfi_rs1_rdata,
    .rvfi_rs2_rdata,
    .rvfi_rs3_rdata,
    .rvfi_rd_addr,
    .rvfi_rd_wdata,
    .rvfi_pc_rdata,
    .rvfi_pc_wdata,
    .rvfi_mem_addr,
    .rvfi_mem_rmask,
    .rvfi_mem_wmask,
    .rvfi_mem_rdata,
    .rvfi_mem_wdata,
    .rvfi_ext_mip,
    .rvfi_ext_nmi,
    .rvfi_ext_debug_req,
    .rvfi_ext_mcycle,
    .rvfi_ext_mhpmcounters,
    .rvfi_ext_mhpmcountersh,
    .rvfi_ext_ic_scr_key_valid,

    .fetch_enable_i,
    .alert_minor_o,
    .alert_major_internal_o,
    .alert_major_bus_o,
    .core_sleep_o
  );

  ibex_tracer
  u_ibex_tracer (
    .clk_i,
    .rst_ni,

    .hart_id_i,

    .rvfi_valid,
    .rvfi_order,
    .rvfi_insn,
    .rvfi_trap,
    .rvfi_halt,
    .rvfi_intr,
    .rvfi_mode,
    .rvfi_ixl,
    .rvfi_rs1_addr,
    .rvfi_rs2_addr,
    .rvfi_rs3_addr,
    .rvfi_rs1_rdata,
    .rvfi_rs2_rdata,
    .rvfi_rs3_rdata,
    .rvfi_rd_addr,
    .rvfi_rd_wdata,
    .rvfi_pc_rdata,
    .rvfi_pc_wdata,
    .rvfi_mem_addr,
    .rvfi_mem_rmask,
    .rvfi_mem_wmask,
    .rvfi_mem_rdata,
    .rvfi_mem_wdata
  );

endmodule
