// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

`include "prim_assert.sv"

/**
 * Top level module of the ibex RISC-V core
 */
module ibex_top import ibex_pkg::*; #(
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
  parameter int unsigned DmExceptionAddr  = 32'h1A110808,
  // Default seed and nonce for scrambling
  parameter logic [SCRAMBLE_KEY_W-1:0]   RndCnstIbexKey   = RndCnstIbexKeyDefault,
  parameter logic [SCRAMBLE_NONCE_W-1:0] RndCnstIbexNonce = RndCnstIbexNonceDefault
) (
  // Clock and Reset
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic                         test_en_i,     // enable all clock gates for testing
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

  // RISC-V Formal Interface
  // Does not comply with the coding standards of _i/_o suffixes, but follows
  // the convention of RISC-V Formal Interface Specification.
`ifdef RVFI
  output logic                         rvfi_valid,
  output logic [63:0]                  rvfi_order,
  output logic [31:0]                  rvfi_insn,
  output logic                         rvfi_trap,
  output logic                         rvfi_halt,
  output logic                         rvfi_intr,
  output logic [ 1:0]                  rvfi_mode,
  output logic [ 1:0]                  rvfi_ixl,
  output logic [ 4:0]                  rvfi_rs1_addr,
  output logic [ 4:0]                  rvfi_rs2_addr,
  output logic [ 4:0]                  rvfi_rs3_addr,
  output logic [31:0]                  rvfi_rs1_rdata,
  output logic [31:0]                  rvfi_rs2_rdata,
  output logic [31:0]                  rvfi_rs3_rdata,
  output logic [ 4:0]                  rvfi_rd_addr,
  output logic [31:0]                  rvfi_rd_wdata,
  output logic [31:0]                  rvfi_pc_rdata,
  output logic [31:0]                  rvfi_pc_wdata,
  output logic [31:0]                  rvfi_mem_addr,
  output logic [ 3:0]                  rvfi_mem_rmask,
  output logic [ 3:0]                  rvfi_mem_wmask,
  output logic [31:0]                  rvfi_mem_rdata,
  output logic [31:0]                  rvfi_mem_wdata,
  output logic [31:0]                  rvfi_ext_mip,
  output logic                         rvfi_ext_nmi,
  output logic                         rvfi_ext_nmi_int,
  output logic                         rvfi_ext_debug_req,
  output logic                         rvfi_ext_debug_mode,
  output logic                         rvfi_ext_rf_wr_suppress,
  output logic [63:0]                  rvfi_ext_mcycle,
  output logic [31:0]                  rvfi_ext_mhpmcounters [10],
  output logic [31:0]                  rvfi_ext_mhpmcountersh [10],
  output logic                         rvfi_ext_ic_scr_key_valid,
`endif

  // CPU Control Signals
  input  ibex_mubi_t                   fetch_enable_i,
  output logic                         alert_minor_o,
  output logic                         alert_major_internal_o,
  output logic                         alert_major_bus_o,
  output logic                         core_sleep_o,

  // DFT bypass controls
  input logic                          scan_rst_ni
);

  localparam bit          Lockstep          = SecureIbex;
  localparam bit          ResetAll          = Lockstep;
  localparam bit          DummyInstructions = SecureIbex;
  localparam bit          RegFileECC        = SecureIbex;
  localparam bit          RegFileWrenCheck  = SecureIbex;
  localparam int unsigned RegFileDataWidth  = RegFileECC ? 32 + 7 : 32;
  localparam bit          MemECC            = SecureIbex;
  localparam int unsigned MemDataWidth      = MemECC ? 32 + 7 : 32;
  // Icache parameters
  localparam int unsigned BusSizeECC        = ICacheECC ? (BUS_SIZE + 7) : BUS_SIZE;
  localparam int unsigned LineSizeECC       = BusSizeECC * IC_LINE_BEATS;
  localparam int unsigned TagSizeECC        = ICacheECC ? (IC_TAG_SIZE + 6) : IC_TAG_SIZE;
  // Scrambling Parameter
  localparam int unsigned NumAddrScrRounds  = ICacheScramble ? 2 : 0;
  localparam int unsigned NumDiffRounds     = NumAddrScrRounds;

  // Clock signals
  logic                        clk;
  ibex_mubi_t                  core_busy_d, core_busy_q;
  logic                        clock_en;
  logic                        irq_pending;
  // Core <-> Register file signals
  logic                        dummy_instr_id;
  logic                        dummy_instr_wb;
  logic [4:0]                  rf_raddr_a;
  logic [4:0]                  rf_raddr_b;
  logic [4:0]                  rf_waddr_wb;
  logic                        rf_we_wb;
  logic [RegFileDataWidth-1:0] rf_wdata_wb_ecc;
  logic [RegFileDataWidth-1:0] rf_rdata_a_ecc, rf_rdata_a_ecc_buf;
  logic [RegFileDataWidth-1:0] rf_rdata_b_ecc, rf_rdata_b_ecc_buf;

  // Combined data and integrity for data and instruction busses
  logic [MemDataWidth-1:0]     data_wdata_core;
  logic [MemDataWidth-1:0]     data_rdata_core;
  logic [MemDataWidth-1:0]     instr_rdata_core;

  // Core <-> RAMs signals
  logic [IC_NUM_WAYS-1:0]      ic_tag_req;
  logic                        ic_tag_write;
  logic [IC_INDEX_W-1:0]       ic_tag_addr;
  logic [TagSizeECC-1:0]       ic_tag_wdata;
  logic [TagSizeECC-1:0]       ic_tag_rdata [IC_NUM_WAYS];
  logic [IC_NUM_WAYS-1:0]      ic_data_req;
  logic                        ic_data_write;
  logic [IC_INDEX_W-1:0]       ic_data_addr;
  logic [LineSizeECC-1:0]      ic_data_wdata;
  logic [LineSizeECC-1:0]      ic_data_rdata [IC_NUM_WAYS];
  logic                        ic_scr_key_req;
  // Alert signals
  logic                        core_alert_major_internal, core_alert_major_bus, core_alert_minor;
  logic                        lockstep_alert_major_internal, lockstep_alert_major_bus;
  logic                        lockstep_alert_minor;
  // Scramble signals
  logic [SCRAMBLE_KEY_W-1:0]   scramble_key_q;
  logic [SCRAMBLE_NONCE_W-1:0] scramble_nonce_q;
  logic                        scramble_key_valid_d, scramble_key_valid_q;
  logic                        scramble_req_d, scramble_req_q;

  ibex_mubi_t                  fetch_enable_buf;

  /////////////////////
  // Main clock gate //
  /////////////////////

  if (SecureIbex) begin : g_clock_en_secure
    // For secure Ibex core_busy_q must be a specific multi-bit pattern to enable the clock.
    prim_flop #(
      .Width($bits(ibex_mubi_t)),
      .ResetValue(IbexMuBiOff)
    ) u_prim_core_busy_flop (
      .clk_i (clk_i),
      .rst_ni(rst_ni),
      .d_i   (core_busy_d),
      .q_o   (core_busy_q)
    );
    assign clock_en = (core_busy_q != IbexMuBiOff) | debug_req_i | irq_pending | irq_nm_i;
  end else begin : g_clock_en_non_secure
    // For non secure Ibex only the bottom bit of core_busy_q is considered. Other FFs can be
    // optimized away during synthesis.
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        core_busy_q <= IbexMuBiOff;
      end else begin
        core_busy_q <= core_busy_d;
      end
    end
    assign clock_en = core_busy_q[0] | debug_req_i | irq_pending | irq_nm_i;

    logic unused_core_busy;
    assign unused_core_busy = ^core_busy_q[$bits(ibex_mubi_t)-1:1];
  end

  assign core_sleep_o = ~clock_en;

  prim_clock_gating core_clock_gate_i (
    .clk_i    (clk_i),
    .en_i     (clock_en),
    .test_en_i(test_en_i),
    .clk_o    (clk)
  );

  ////////////////////////
  // Core instantiation //
  ////////////////////////

  // Buffer security critical signals to prevent synthesis optimisation removing them
  prim_buf #(.Width($bits(ibex_mubi_t))) u_fetch_enable_buf (
    .in_i (fetch_enable_i),
    .out_o(fetch_enable_buf)
  );

  prim_buf #(.Width(RegFileDataWidth)) u_rf_rdata_a_ecc_buf (
    .in_i (rf_rdata_a_ecc),
    .out_o(rf_rdata_a_ecc_buf)
  );

  prim_buf #(.Width(RegFileDataWidth)) u_rf_rdata_b_ecc_buf (
    .in_i (rf_rdata_b_ecc),
    .out_o(rf_rdata_b_ecc_buf)
  );


  // ibex_core takes integrity and data bits together. Combine the separate integrity and data
  // inputs here.
  assign data_rdata_core[31:0] = data_rdata_i;
  assign instr_rdata_core[31:0] = instr_rdata_i;

  if (MemECC) begin : gen_mem_rdata_ecc
    assign data_rdata_core[38:32] = data_rdata_intg_i;
    assign instr_rdata_core[38:32] = instr_rdata_intg_i;
  end else begin : gen_non_mem_rdata_ecc
    logic unused_intg;

    assign unused_intg = ^{instr_rdata_intg_i, data_rdata_intg_i};
  end

  ibex_core #(
    .PMPEnable        (PMPEnable),
    .PMPGranularity   (PMPGranularity),
    .PMPNumRegions    (PMPNumRegions),
    .MHPMCounterNum   (MHPMCounterNum),
    .MHPMCounterWidth (MHPMCounterWidth),
    .RV32E            (RV32E),
    .RV32M            (RV32M),
    .RV32B            (RV32B),
    .BranchTargetALU  (BranchTargetALU),
    .ICache           (ICache),
    .ICacheECC        (ICacheECC),
    .BusSizeECC       (BusSizeECC),
    .TagSizeECC       (TagSizeECC),
    .LineSizeECC      (LineSizeECC),
    .BranchPredictor  (BranchPredictor),
    .DbgTriggerEn     (DbgTriggerEn),
    .DbgHwBreakNum    (DbgHwBreakNum),
    .WritebackStage   (WritebackStage),
    .ResetAll         (ResetAll),
    .RndCnstLfsrSeed  (RndCnstLfsrSeed),
    .RndCnstLfsrPerm  (RndCnstLfsrPerm),
    .SecureIbex       (SecureIbex),
    .DummyInstructions(DummyInstructions),
    .RegFileECC       (RegFileECC),
    .RegFileDataWidth (RegFileDataWidth),
    .MemECC           (MemECC),
    .MemDataWidth     (MemDataWidth),
    .DmHaltAddr       (DmHaltAddr),
    .DmExceptionAddr  (DmExceptionAddr)
  ) u_ibex_core (
    .clk_i(clk),
    .rst_ni,

    .hart_id_i,
    .boot_addr_i,

    .instr_req_o,
    .instr_gnt_i,
    .instr_rvalid_i,
    .instr_addr_o,
    .instr_rdata_i(instr_rdata_core),
    .instr_err_i,

    .data_req_o,
    .data_gnt_i,
    .data_rvalid_i,
    .data_we_o,
    .data_be_o,
    .data_addr_o,
    .data_wdata_o(data_wdata_core),
    .data_rdata_i(data_rdata_core),
    .data_err_i,

    .dummy_instr_id_o (dummy_instr_id),
    .dummy_instr_wb_o (dummy_instr_wb),
    .rf_raddr_a_o     (rf_raddr_a),
    .rf_raddr_b_o     (rf_raddr_b),
    .rf_waddr_wb_o    (rf_waddr_wb),
    .rf_we_wb_o       (rf_we_wb),
    .rf_wdata_wb_ecc_o(rf_wdata_wb_ecc),
    .rf_rdata_a_ecc_i (rf_rdata_a_ecc_buf),
    .rf_rdata_b_ecc_i (rf_rdata_b_ecc_buf),

    .ic_tag_req_o      (ic_tag_req),
    .ic_tag_write_o    (ic_tag_write),
    .ic_tag_addr_o     (ic_tag_addr),
    .ic_tag_wdata_o    (ic_tag_wdata),
    .ic_tag_rdata_i    (ic_tag_rdata),
    .ic_data_req_o     (ic_data_req),
    .ic_data_write_o   (ic_data_write),
    .ic_data_addr_o    (ic_data_addr),
    .ic_data_wdata_o   (ic_data_wdata),
    .ic_data_rdata_i   (ic_data_rdata),
    .ic_scr_key_valid_i(scramble_key_valid_q),
    .ic_scr_key_req_o  (ic_scr_key_req),

    .irq_software_i,
    .irq_timer_i,
    .irq_external_i,
    .irq_fast_i,
    .irq_nm_i,
    .irq_pending_o(irq_pending),

    .debug_req_i,
    .crash_dump_o,
    .double_fault_seen_o,

`ifdef RVFI
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
    .rvfi_ext_nmi_int,
    .rvfi_ext_debug_req,
    .rvfi_ext_debug_mode,
    .rvfi_ext_rf_wr_suppress,
    .rvfi_ext_mcycle,
    .rvfi_ext_mhpmcounters,
    .rvfi_ext_mhpmcountersh,
    .rvfi_ext_ic_scr_key_valid,
`endif

    .fetch_enable_i        (fetch_enable_buf),
    .alert_minor_o         (core_alert_minor),
    .alert_major_internal_o(core_alert_major_internal),
    .alert_major_bus_o     (core_alert_major_bus),
    .core_busy_o           (core_busy_d)
  );

  /////////////////////////////////
  // Register file Instantiation //
  /////////////////////////////////

  logic rf_alert_major_internal;
  if (RegFile == RegFileFF) begin : gen_regfile_ff
    ibex_register_file_ff #(
      .RV32E            (RV32E),
      .DataWidth        (RegFileDataWidth),
      .DummyInstructions(DummyInstructions),
      // SEC_CM: DATA_REG_SW.GLITCH_DETECT
      .WrenCheck        (RegFileWrenCheck),
      .WordZeroVal      (RegFileDataWidth'(prim_secded_pkg::SecdedInv3932ZeroWord))
    ) register_file_i (
      .clk_i (clk),
      .rst_ni(rst_ni),

      .test_en_i       (test_en_i),
      .dummy_instr_id_i(dummy_instr_id),
      .dummy_instr_wb_i(dummy_instr_wb),

      .raddr_a_i(rf_raddr_a),
      .rdata_a_o(rf_rdata_a_ecc),
      .raddr_b_i(rf_raddr_b),
      .rdata_b_o(rf_rdata_b_ecc),
      .waddr_a_i(rf_waddr_wb),
      .wdata_a_i(rf_wdata_wb_ecc),
      .we_a_i   (rf_we_wb),
      .err_o    (rf_alert_major_internal)
    );
  end else if (RegFile == RegFileFPGA) begin : gen_regfile_fpga
    ibex_register_file_fpga #(
      .RV32E            (RV32E),
      .DataWidth        (RegFileDataWidth),
      .DummyInstructions(DummyInstructions),
      // SEC_CM: DATA_REG_SW.GLITCH_DETECT
      .WrenCheck        (RegFileWrenCheck),
      .WordZeroVal      (RegFileDataWidth'(prim_secded_pkg::SecdedInv3932ZeroWord))
    ) register_file_i (
      .clk_i (clk),
      .rst_ni(rst_ni),

      .test_en_i       (test_en_i),
      .dummy_instr_id_i(dummy_instr_id),
      .dummy_instr_wb_i(dummy_instr_wb),

      .raddr_a_i(rf_raddr_a),
      .rdata_a_o(rf_rdata_a_ecc),
      .raddr_b_i(rf_raddr_b),
      .rdata_b_o(rf_rdata_b_ecc),
      .waddr_a_i(rf_waddr_wb),
      .wdata_a_i(rf_wdata_wb_ecc),
      .we_a_i   (rf_we_wb),
      .err_o    (rf_alert_major_internal)
    );
  end else if (RegFile == RegFileLatch) begin : gen_regfile_latch
    ibex_register_file_latch #(
      .RV32E            (RV32E),
      .DataWidth        (RegFileDataWidth),
      .DummyInstructions(DummyInstructions),
      // SEC_CM: DATA_REG_SW.GLITCH_DETECT
      .WrenCheck        (RegFileWrenCheck),
      .WordZeroVal      (RegFileDataWidth'(prim_secded_pkg::SecdedInv3932ZeroWord))
    ) register_file_i (
      .clk_i (clk),
      .rst_ni(rst_ni),

      .test_en_i       (test_en_i),
      .dummy_instr_id_i(dummy_instr_id),
      .dummy_instr_wb_i(dummy_instr_wb),

      .raddr_a_i(rf_raddr_a),
      .rdata_a_o(rf_rdata_a_ecc),
      .raddr_b_i(rf_raddr_b),
      .rdata_b_o(rf_rdata_b_ecc),
      .waddr_a_i(rf_waddr_wb),
      .wdata_a_i(rf_wdata_wb_ecc),
      .we_a_i   (rf_we_wb),
      .err_o    (rf_alert_major_internal)
    );
  end

  ///////////////////////////////
  // Scrambling Infrastructure //
  ///////////////////////////////

  if (ICacheScramble) begin : gen_scramble

    // SEC_CM: ICACHE.MEM.SCRAMBLE
    // Scramble key valid starts with OTP returning new valid key and stays high
    // until we request a new valid key.
    assign scramble_key_valid_d = scramble_req_q ? scramble_key_valid_i :
                                  ic_scr_key_req ? 1'b0                 :
                                                   scramble_key_valid_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        scramble_key_q       <= RndCnstIbexKey;
        scramble_nonce_q     <= RndCnstIbexNonce;
      end else if (scramble_key_valid_i) begin
        scramble_key_q       <= scramble_key_i;
        scramble_nonce_q     <= scramble_nonce_i;
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        scramble_key_valid_q <= 1'b1;
        scramble_req_q       <= '0;
      end else begin
        scramble_key_valid_q <= scramble_key_valid_d;
        scramble_req_q       <= scramble_req_d;
      end
    end

  // Scramble key request starts with invalidate signal from ICache and stays high
  // until we got a valid key.
    assign scramble_req_d = scramble_req_q ? ~scramble_key_valid_i : ic_scr_key_req;
    assign scramble_req_o = scramble_req_q;

  end else begin : gen_noscramble

    logic unused_scramble_inputs = scramble_key_valid_i & (|scramble_key_i) & (|RndCnstIbexKey) &
                                   (|scramble_nonce_i) & (|RndCnstIbexNonce) & scramble_req_q &
                                   ic_scr_key_req & scramble_key_valid_d & scramble_req_d;

    assign scramble_req_d       = 1'b0;
    assign scramble_req_q       = 1'b0;
    assign scramble_req_o       = 1'b0;
    assign scramble_key_q       = '0;
    assign scramble_nonce_q     = '0;
    assign scramble_key_valid_q = 1'b1;
    assign scramble_key_valid_d = 1'b1;
  end

  ////////////////////////
  // Rams Instantiation //
  ////////////////////////

  if (ICache) begin : gen_rams

    for (genvar way = 0; way < IC_NUM_WAYS; way++) begin : gen_rams_inner

      if (ICacheScramble) begin : gen_scramble_rams

        // SEC_CM: ICACHE.MEM.SCRAMBLE
        // Tag RAM instantiation
        prim_ram_1p_scr #(
          .Width            (TagSizeECC),
          .Depth            (IC_NUM_LINES),
          .DataBitsPerMask  (TagSizeECC),
          .EnableParity     (0),
          .DiffWidth        (TagSizeECC),
          .NumAddrScrRounds (NumAddrScrRounds),
          .NumDiffRounds    (NumDiffRounds)
        ) tag_bank (
          .clk_i,
          .rst_ni,

          .key_valid_i (scramble_key_valid_q),
          .key_i       (scramble_key_q),
          .nonce_i     (scramble_nonce_q),

          .req_i       (ic_tag_req[way]),

          .gnt_o       (),
          .write_i     (ic_tag_write),
          .addr_i      (ic_tag_addr),
          .wdata_i     (ic_tag_wdata),
          .wmask_i     ({TagSizeECC{1'b1}}),
          .intg_error_i(1'b0),

          .rdata_o     (ic_tag_rdata[way]),
          .rvalid_o    (),
          .raddr_o     (),
          .rerror_o    (),
          .cfg_i       (ram_cfg_i)
        );

        // Data RAM instantiation
        prim_ram_1p_scr #(
          .Width              (LineSizeECC),
          .Depth              (IC_NUM_LINES),
          .DataBitsPerMask    (LineSizeECC),
          .ReplicateKeyStream (1),
          .EnableParity       (0),
          .DiffWidth          (LineSizeECC),
          .NumAddrScrRounds   (NumAddrScrRounds),
          .NumDiffRounds      (NumDiffRounds)
        ) data_bank (
          .clk_i,
          .rst_ni,

          .key_valid_i (scramble_key_valid_q),
          .key_i       (scramble_key_q),
          .nonce_i     (scramble_nonce_q),

          .req_i       (ic_data_req[way]),

          .gnt_o       (),
          .write_i     (ic_data_write),
          .addr_i      (ic_data_addr),
          .wdata_i     (ic_data_wdata),
          .wmask_i     ({LineSizeECC{1'b1}}),
          .intg_error_i(1'b0),

          .rdata_o     (ic_data_rdata[way]),
          .rvalid_o    (),
          .raddr_o     (),
          .rerror_o    (),
          .cfg_i       (ram_cfg_i)
        );

        `ifdef INC_ASSERT
          // Sample scramble key whenever it is valid for use in the assertions below.  This may be
          // redundant with the sampling performed in the actual design, but that is okay because
          // the assertions exist to check the correct functioning of the design.
          logic [SCRAMBLE_KEY_W-1:0] sampled_scramble_key;
          always_ff @(posedge clk_i, negedge rst_ni) begin
            if (!rst_ni) begin
              sampled_scramble_key <= 'x;
            end else if (scramble_key_valid_i) begin
              sampled_scramble_key <= scramble_key_i;
            end
          end

          // Ensure that when a scramble key is received, it is correctly applied to the icache
          // scrambled memory primitives.  The upper bound in the cycle ranges below is not exact,
          // but it should not take more than 10 cycles.
          `ASSERT(ScrambleKeyAppliedAtTagBank_A,
                  scramble_key_valid_i
                  |-> ##[0:10]
                  tag_bank.key_valid_i && (tag_bank.key_i == sampled_scramble_key),
                  clk_i, !rst_ni
          )
          `ASSERT(ScrambleKeyAppliedAtDataBank_A,
                  scramble_key_valid_i
                  |-> ##[0:10]
                  data_bank.key_valid_i && (data_bank.key_i == sampled_scramble_key),
                  clk_i, !rst_ni
          )
        `endif

      end else begin : gen_noscramble_rams

        // Tag RAM instantiation
        prim_ram_1p #(
          .Width            (TagSizeECC),
          .Depth            (IC_NUM_LINES),
          .DataBitsPerMask  (TagSizeECC)
        ) tag_bank (
          .clk_i,

          .req_i       (ic_tag_req[way]),

          .write_i     (ic_tag_write),
          .addr_i      (ic_tag_addr),
          .wdata_i     (ic_tag_wdata),
          .wmask_i     ({TagSizeECC{1'b1}}),

          .rdata_o     (ic_tag_rdata[way]),
          .cfg_i       (ram_cfg_i)
        );

        // Data RAM instantiation
        prim_ram_1p #(
          .Width              (LineSizeECC),
          .Depth              (IC_NUM_LINES),
          .DataBitsPerMask    (LineSizeECC)
        ) data_bank (
          .clk_i,

          .req_i       (ic_data_req[way]),

          .write_i     (ic_data_write),
          .addr_i      (ic_data_addr),
          .wdata_i     (ic_data_wdata),
          .wmask_i     ({LineSizeECC{1'b1}}),

          .rdata_o     (ic_data_rdata[way]),
          .cfg_i       (ram_cfg_i)
        );

      end
    end

  end else begin : gen_norams

    prim_ram_1p_pkg::ram_1p_cfg_t unused_ram_cfg;
    logic unused_ram_inputs;

    assign unused_ram_cfg    = ram_cfg_i;
    assign unused_ram_inputs = (|ic_tag_req) & ic_tag_write & (|ic_tag_addr) & (|ic_tag_wdata) &
                               (|ic_data_req) & ic_data_write & (|ic_data_addr) & (|ic_data_wdata) &
                               (|scramble_key_q) & (|scramble_nonce_q) & scramble_key_valid_q &
                               scramble_key_valid_d & (|scramble_nonce_q) &
                               (|NumAddrScrRounds);

    assign ic_tag_rdata      = '{default:'b0};
    assign ic_data_rdata     = '{default:'b0};

  end

  assign data_wdata_o = data_wdata_core[31:0];

  if (MemECC) begin : gen_mem_wdata_ecc
    prim_buf #(.Width(7)) u_prim_buf_data_wdata_intg (
      .in_i (data_wdata_core[38:32]),
      .out_o(data_wdata_intg_o)
    );
  end else begin : gen_no_mem_ecc
    assign data_wdata_intg_o = '0;
  end

  // Redundant lockstep core implementation
  if (Lockstep) begin : gen_lockstep
    // SEC_CM: LOGIC.SHADOW
    // Note: certain synthesis tools like DC are very smart at optimizing away redundant logic.
    // Hence, we have to insert an optimization barrier at the IOs of the lockstep Ibex.
    // This is achieved by manually buffering each bit using prim_buf.
    // Our Xilinx and DC synthesis flows make sure that these buffers cannot be optimized away
    // using keep attributes (Vivado) and size_only constraints (DC).

    localparam int NumBufferBits = $bits({
      hart_id_i,
      boot_addr_i,
      instr_req_o,
      instr_gnt_i,
      instr_rvalid_i,
      instr_addr_o,
      instr_rdata_core,
      instr_err_i,
      data_req_o,
      data_gnt_i,
      data_rvalid_i,
      data_we_o,
      data_be_o,
      data_addr_o,
      data_wdata_core,
      data_rdata_core,
      data_err_i,
      dummy_instr_id,
      dummy_instr_wb,
      rf_raddr_a,
      rf_raddr_b,
      rf_waddr_wb,
      rf_we_wb,
      rf_wdata_wb_ecc,
      rf_rdata_a_ecc,
      rf_rdata_b_ecc,
      ic_tag_req,
      ic_tag_write,
      ic_tag_addr,
      ic_tag_wdata,
      ic_data_req,
      ic_data_write,
      ic_data_addr,
      ic_data_wdata,
      scramble_key_valid_i,
      ic_scr_key_req,
      irq_software_i,
      irq_timer_i,
      irq_external_i,
      irq_fast_i,
      irq_nm_i,
      irq_pending,
      debug_req_i,
      crash_dump_o,
      double_fault_seen_o,
      fetch_enable_i,
      core_busy_d
    });

    logic [NumBufferBits-1:0] buf_in, buf_out;

    logic [31:0]                  hart_id_local;
    logic [31:0]                  boot_addr_local;

    logic                         instr_req_local;
    logic                         instr_gnt_local;
    logic                         instr_rvalid_local;
    logic [31:0]                  instr_addr_local;
    logic [MemDataWidth-1:0]      instr_rdata_local;
    logic                         instr_err_local;

    logic                         data_req_local;
    logic                         data_gnt_local;
    logic                         data_rvalid_local;
    logic                         data_we_local;
    logic [3:0]                   data_be_local;
    logic [31:0]                  data_addr_local;
    logic [MemDataWidth-1:0]      data_wdata_local;
    logic [MemDataWidth-1:0]      data_rdata_local;
    logic                         data_err_local;

    logic                         dummy_instr_id_local;
    logic                         dummy_instr_wb_local;
    logic [4:0]                   rf_raddr_a_local;
    logic [4:0]                   rf_raddr_b_local;
    logic [4:0]                   rf_waddr_wb_local;
    logic                         rf_we_wb_local;
    logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_local;
    logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_local;
    logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_local;

    logic [IC_NUM_WAYS-1:0]       ic_tag_req_local;
    logic                         ic_tag_write_local;
    logic [IC_INDEX_W-1:0]        ic_tag_addr_local;
    logic [TagSizeECC-1:0]        ic_tag_wdata_local;
    logic [IC_NUM_WAYS-1:0]       ic_data_req_local;
    logic                         ic_data_write_local;
    logic [IC_INDEX_W-1:0]        ic_data_addr_local;
    logic [LineSizeECC-1:0]       ic_data_wdata_local;
    logic                         scramble_key_valid_local;
    logic                         ic_scr_key_req_local;

    logic                         irq_software_local;
    logic                         irq_timer_local;
    logic                         irq_external_local;
    logic [14:0]                  irq_fast_local;
    logic                         irq_nm_local;
    logic                         irq_pending_local;

    logic                         debug_req_local;
    crash_dump_t                  crash_dump_local;
    logic                         double_fault_seen_local;
    ibex_mubi_t                   fetch_enable_local;

    ibex_mubi_t                   core_busy_local;

    assign buf_in = {
      hart_id_i,
      boot_addr_i,
      instr_req_o,
      instr_gnt_i,
      instr_rvalid_i,
      instr_addr_o,
      instr_rdata_core,
      instr_err_i,
      data_req_o,
      data_gnt_i,
      data_rvalid_i,
      data_we_o,
      data_be_o,
      data_addr_o,
      data_wdata_core,
      data_rdata_core,
      data_err_i,
      dummy_instr_id,
      dummy_instr_wb,
      rf_raddr_a,
      rf_raddr_b,
      rf_waddr_wb,
      rf_we_wb,
      rf_wdata_wb_ecc,
      rf_rdata_a_ecc,
      rf_rdata_b_ecc,
      ic_tag_req,
      ic_tag_write,
      ic_tag_addr,
      ic_tag_wdata,
      ic_data_req,
      ic_data_write,
      ic_data_addr,
      ic_data_wdata,
      scramble_key_valid_q,
      ic_scr_key_req,
      irq_software_i,
      irq_timer_i,
      irq_external_i,
      irq_fast_i,
      irq_nm_i,
      irq_pending,
      debug_req_i,
      crash_dump_o,
      double_fault_seen_o,
      fetch_enable_i,
      core_busy_d
    };

    assign {
      hart_id_local,
      boot_addr_local,
      instr_req_local,
      instr_gnt_local,
      instr_rvalid_local,
      instr_addr_local,
      instr_rdata_local,
      instr_err_local,
      data_req_local,
      data_gnt_local,
      data_rvalid_local,
      data_we_local,
      data_be_local,
      data_addr_local,
      data_wdata_local,
      data_rdata_local,
      data_err_local,
      dummy_instr_id_local,
      dummy_instr_wb_local,
      rf_raddr_a_local,
      rf_raddr_b_local,
      rf_waddr_wb_local,
      rf_we_wb_local,
      rf_wdata_wb_ecc_local,
      rf_rdata_a_ecc_local,
      rf_rdata_b_ecc_local,
      ic_tag_req_local,
      ic_tag_write_local,
      ic_tag_addr_local,
      ic_tag_wdata_local,
      ic_data_req_local,
      ic_data_write_local,
      ic_data_addr_local,
      ic_data_wdata_local,
      scramble_key_valid_local,
      ic_scr_key_req_local,
      irq_software_local,
      irq_timer_local,
      irq_external_local,
      irq_fast_local,
      irq_nm_local,
      irq_pending_local,
      debug_req_local,
      crash_dump_local,
      double_fault_seen_local,
      fetch_enable_local,
      core_busy_local
    } = buf_out;

    // Manually buffer all input signals.
    prim_buf #(.Width(NumBufferBits)) u_signals_prim_buf (
      .in_i(buf_in),
      .out_o(buf_out)
    );

    logic [TagSizeECC-1:0]  ic_tag_rdata_local [IC_NUM_WAYS];
    logic [LineSizeECC-1:0] ic_data_rdata_local [IC_NUM_WAYS];
    for (genvar k = 0; k < IC_NUM_WAYS; k++) begin : gen_ways
      prim_buf #(.Width(TagSizeECC)) u_tag_prim_buf (
        .in_i(ic_tag_rdata[k]),
        .out_o(ic_tag_rdata_local[k])
      );
      prim_buf #(.Width(LineSizeECC)) u_data_prim_buf (
        .in_i(ic_data_rdata[k]),
        .out_o(ic_data_rdata_local[k])
      );
    end

    logic lockstep_alert_minor_local, lockstep_alert_major_internal_local;
    logic lockstep_alert_major_bus_local;

    ibex_lockstep #(
      .PMPEnable        (PMPEnable),
      .PMPGranularity   (PMPGranularity),
      .PMPNumRegions    (PMPNumRegions),
      .MHPMCounterNum   (MHPMCounterNum),
      .MHPMCounterWidth (MHPMCounterWidth),
      .RV32E            (RV32E),
      .RV32M            (RV32M),
      .RV32B            (RV32B),
      .BranchTargetALU  (BranchTargetALU),
      .ICache           (ICache),
      .ICacheECC        (ICacheECC),
      .BusSizeECC       (BusSizeECC),
      .TagSizeECC       (TagSizeECC),
      .LineSizeECC      (LineSizeECC),
      .BranchPredictor  (BranchPredictor),
      .DbgTriggerEn     (DbgTriggerEn),
      .DbgHwBreakNum    (DbgHwBreakNum),
      .WritebackStage   (WritebackStage),
      .ResetAll         (ResetAll),
      .RndCnstLfsrSeed  (RndCnstLfsrSeed),
      .RndCnstLfsrPerm  (RndCnstLfsrPerm),
      .SecureIbex       (SecureIbex),
      .DummyInstructions(DummyInstructions),
      .RegFileECC       (RegFileECC),
      .RegFileDataWidth (RegFileDataWidth),
      .MemECC           (MemECC),
      .DmHaltAddr       (DmHaltAddr),
      .DmExceptionAddr  (DmExceptionAddr)
    ) u_ibex_lockstep (
      .clk_i                  (clk),
      .rst_ni                 (rst_ni),

      .hart_id_i              (hart_id_local),
      .boot_addr_i            (boot_addr_local),

      .instr_req_i            (instr_req_local),
      .instr_gnt_i            (instr_gnt_local),
      .instr_rvalid_i         (instr_rvalid_local),
      .instr_addr_i           (instr_addr_local),
      .instr_rdata_i          (instr_rdata_local),
      .instr_err_i            (instr_err_local),

      .data_req_i             (data_req_local),
      .data_gnt_i             (data_gnt_local),
      .data_rvalid_i          (data_rvalid_local),
      .data_we_i              (data_we_local),
      .data_be_i              (data_be_local),
      .data_addr_i            (data_addr_local),
      .data_wdata_i           (data_wdata_local),
      .data_rdata_i           (data_rdata_local),
      .data_err_i             (data_err_local),

      .dummy_instr_id_i       (dummy_instr_id_local),
      .dummy_instr_wb_i       (dummy_instr_wb_local),
      .rf_raddr_a_i           (rf_raddr_a_local),
      .rf_raddr_b_i           (rf_raddr_b_local),
      .rf_waddr_wb_i          (rf_waddr_wb_local),
      .rf_we_wb_i             (rf_we_wb_local),
      .rf_wdata_wb_ecc_i      (rf_wdata_wb_ecc_local),
      .rf_rdata_a_ecc_i       (rf_rdata_a_ecc_local),
      .rf_rdata_b_ecc_i       (rf_rdata_b_ecc_local),

      .ic_tag_req_i           (ic_tag_req_local),
      .ic_tag_write_i         (ic_tag_write_local),
      .ic_tag_addr_i          (ic_tag_addr_local),
      .ic_tag_wdata_i         (ic_tag_wdata_local),
      .ic_tag_rdata_i         (ic_tag_rdata_local),
      .ic_data_req_i          (ic_data_req_local),
      .ic_data_write_i        (ic_data_write_local),
      .ic_data_addr_i         (ic_data_addr_local),
      .ic_data_wdata_i        (ic_data_wdata_local),
      .ic_data_rdata_i        (ic_data_rdata_local),
      .ic_scr_key_valid_i     (scramble_key_valid_local),
      .ic_scr_key_req_i       (ic_scr_key_req_local),

      .irq_software_i         (irq_software_local),
      .irq_timer_i            (irq_timer_local),
      .irq_external_i         (irq_external_local),
      .irq_fast_i             (irq_fast_local),
      .irq_nm_i               (irq_nm_local),
      .irq_pending_i          (irq_pending_local),

      .debug_req_i            (debug_req_local),
      .crash_dump_i           (crash_dump_local),
      .double_fault_seen_i    (double_fault_seen_local),

      .fetch_enable_i         (fetch_enable_local),
      .alert_minor_o          (lockstep_alert_minor_local),
      .alert_major_internal_o (lockstep_alert_major_internal_local),
      .alert_major_bus_o      (lockstep_alert_major_bus_local),
      .core_busy_i            (core_busy_local),
      .test_en_i              (test_en_i),
      .scan_rst_ni            (scan_rst_ni)
    );

    prim_buf u_prim_buf_alert_minor (
      .in_i (lockstep_alert_minor_local),
      .out_o(lockstep_alert_minor)
    );

    prim_buf u_prim_buf_alert_major_internal (
      .in_i (lockstep_alert_major_internal_local),
      .out_o(lockstep_alert_major_internal)
    );

    prim_buf u_prim_buf_alert_major_bus (
      .in_i (lockstep_alert_major_bus_local),
      .out_o(lockstep_alert_major_bus)
    );

  end else begin : gen_no_lockstep
    assign lockstep_alert_major_internal = 1'b0;
    assign lockstep_alert_major_bus      = 1'b0;
    assign lockstep_alert_minor          = 1'b0;
    logic unused_scan;
    assign unused_scan = scan_rst_ni;
  end

  assign alert_major_internal_o = core_alert_major_internal |
                                  lockstep_alert_major_internal |
                                  rf_alert_major_internal;
  assign alert_major_bus_o      = core_alert_major_bus | lockstep_alert_major_bus;
  assign alert_minor_o          = core_alert_minor | lockstep_alert_minor;

  // X checks for top-level outputs
  `ASSERT_KNOWN(IbexInstrReqX, instr_req_o)
  `ASSERT_KNOWN_IF(IbexInstrReqPayloadX, instr_addr_o, instr_req_o)

  `ASSERT_KNOWN(IbexDataReqX, data_req_o)
  `ASSERT_KNOWN_IF(IbexDataReqPayloadX,
    {data_we_o, data_be_o, data_addr_o, data_wdata_o, data_wdata_intg_o}, data_req_o)

  `ASSERT_KNOWN(IbexScrambleReqX, scramble_req_o)
  `ASSERT_KNOWN(IbexDoubleFaultSeenX, double_fault_seen_o)
  `ASSERT_KNOWN(IbexAlertMinorX, alert_minor_o)
  `ASSERT_KNOWN(IbexAlertMajorInternalX, alert_major_internal_o)
  `ASSERT_KNOWN(IbexAlertMajorBusX, alert_major_bus_o)
  `ASSERT_KNOWN(IbexCoreSleepX, core_sleep_o)

  // X check for top-level inputs
  `ASSERT_KNOWN(IbexTestEnX, test_en_i)
  `ASSERT_KNOWN(IbexRamCfgX, ram_cfg_i)
  `ASSERT_KNOWN(IbexHartIdX, hart_id_i)
  `ASSERT_KNOWN(IbexBootAddrX, boot_addr_i)

  `ASSERT_KNOWN(IbexInstrGntX, instr_gnt_i)
  `ASSERT_KNOWN(IbexInstrRValidX, instr_rvalid_i)
  `ASSERT_KNOWN_IF(IbexInstrRPayloadX,
    {instr_rdata_i, instr_rdata_intg_i, instr_err_i}, instr_rvalid_i)

  `ASSERT_KNOWN(IbexDataGntX, data_gnt_i)
  `ASSERT_KNOWN(IbexDataRValidX, data_rvalid_i)
  `ifdef INC_ASSERT
    // Ibex can have a maximum of 2 accesses outstanding on the DSide. This is because it does not
    // speculative data accesses so the only requests that can be in flight must relate to a single
    // ongoing load or store instruction. Due to unaligned access support a single load or store can
    // generate 2 accesses.
    localparam int unsigned MaxOutstandingDSideAccesses = 2;

    typedef struct packed {
      logic valid;
      logic is_read;
    } pending_access_t;

    pending_access_t pending_dside_accesses_q[MaxOutstandingDSideAccesses];
    pending_access_t pending_dside_accesses_d[MaxOutstandingDSideAccesses];
    pending_access_t pending_dside_accesses_shifted[MaxOutstandingDSideAccesses];

    for (genvar i = 0; i < MaxOutstandingDSideAccesses; i++) begin : g_dside_tracker
      always_ff @(posedge clk or negedge rst_ni) begin
        if (!rst_ni) begin
          pending_dside_accesses_q[i] <= '0;
        end else begin
          pending_dside_accesses_q[i] <= pending_dside_accesses_d[i];
        end
      end

      always_comb begin
        pending_dside_accesses_shifted[i] = pending_dside_accesses_q[i];

        if (data_rvalid_i) begin
          if (i != MaxOutstandingDSideAccesses - 1) begin
            pending_dside_accesses_shifted[i] = pending_dside_accesses_q[i + 1];
          end else begin
            pending_dside_accesses_shifted[i] = '0;
          end
        end
      end

      if (i == 0) begin : g_track_first_entry
        always_comb begin
          pending_dside_accesses_d[i] = pending_dside_accesses_shifted[i];

          if (data_req_o && data_gnt_i && !pending_dside_accesses_shifted[i].valid) begin
            pending_dside_accesses_d[i].valid = 1'b1;
            pending_dside_accesses_d[i].is_read = ~data_we_o;
          end
        end
      end else begin : g_track_other_entries
        always_comb begin
          pending_dside_accesses_d[i] = pending_dside_accesses_shifted[i];

          if (data_req_o && data_gnt_i && pending_dside_accesses_shifted[i - 1].valid &&
              !pending_dside_accesses_shifted[i].valid) begin
            pending_dside_accesses_d[i].valid = 1'b1;
            pending_dside_accesses_d[i].is_read = ~data_we_o;
          end
        end
      end
    end

    // We should never start a new data request if we've already got the maximum outstanding. We can
    // start a new request in the same cycle an old one ends, in which case we'll see all pending
    // accesses valid but one will be ending this cycle so the empty slot can be immediately used by
    // the new request.
    `ASSERT(MaxOutstandingDSideAccessesCorrect,
        data_req_o |->
        ~pending_dside_accesses_q[MaxOutstandingDSideAccesses-1].valid | data_rvalid_i)

    // Should only see a request response if we're expecting one
    `ASSERT(PendingAccessTrackingCorrect, data_rvalid_i |-> pending_dside_accesses_q[0])

    if (SecureIbex) begin : g_secure_ibex_mem_assert
      // For SecureIbex responses to both writes and reads must specify rdata and rdata_intg (for
      // writes rdata is effectively ignored by rdata_intg still checked against rdata)
      `ASSERT_KNOWN_IF(IbexDataRPayloadX, {data_rdata_i, data_rdata_intg_i},
          data_rvalid_i)
    end else begin : g_no_secure_ibex_mem_assert
      // Without SecureIbex data_rdata_i and data_rdata_intg_i are only relevant to reads. Check
      // neither are X on a response to a read.
      `ASSERT_KNOWN_IF(IbexDataRPayloadX, {data_rdata_i, data_rdata_intg_i},
          data_rvalid_i & pending_dside_accesses_q[0].is_read)
    end

    // data_err_i relevant to both reads and writes. Check it isn't X on any response.
    `ASSERT_KNOWN_IF(IbexDataRErrPayloadX, data_err_i, data_rvalid_i)

    `ifdef RVFI
    // Tracking logic and predictor for double_fault_seen_o output, relies on RVFI so only include
    // it where RVFI is available.

    // Returns 1'b1 if the provided instruction decodes to one that would write the sync_exc_bit of
    // the CPUCTRLSTS CSR
    function automatic logic insn_write_sync_exc_seen(logic [31:0] insn_bits);
      return (insn_bits[6:0] == OPCODE_SYSTEM) &&
             (insn_bits[14:12] inside {3'b001, 3'b010, 3'b011, 3'b101}) &&
             (insn_bits[31:20] == CSR_CPUCTRLSTS);
    endfunction

    // Given an instruction that writes the sync_exc_bit of the CPUCTRLSTS CSR along with the value
    // of the rs1 register read for that instruction and the current predicted sync_exc_bit bit
    // return the new value of the sync_exc_bit after the instruction is executed.
    function automatic logic new_sync_exc_bit(logic [31:0] insn_bits, logic [31:0] rs1,
        logic cur_bit);
      logic sync_exc_update_bit;

      sync_exc_update_bit = insn_bits[14] ? 1'b0 : rs1[6];

      case (insn_bits[13:12])
        2'b01: return sync_exc_update_bit;
        2'b10: return cur_bit | sync_exc_update_bit;
        2'b11: return cur_bit & ~sync_exc_update_bit;
        default: return 1'bx;
      endcase
    endfunction

    localparam int DoubleFaultSeenLatency = 3;
    logic [DoubleFaultSeenLatency-1:0] double_fault_seen_delay_buffer;
    logic [DoubleFaultSeenLatency-2:0] double_fault_seen_delay_buffer_q;
    logic                              sync_exc_seen;
    logic                              new_sync_exc;
    logic                              double_fault_seen_predicted;

    assign new_sync_exc                = rvfi_valid & rvfi_trap & ~rvfi_ext_debug_mode;
    assign double_fault_seen_predicted = sync_exc_seen & new_sync_exc;

    // Depending on whether the exception comes from the WB or ID/EX stage the precise timing of the
    // double_fault_seen_o output vs the double fault instruction being visible on RVFI differs. At
    // the earliest extreme it can be asserted the same cycle the instruction is visible on the
    // RVFI.  Buffer the last few cycles of double_fault_seen_o output for checking. We can
    // guarantee the minimum spacing between double_fault_seen_o assertions  (occurring when the
    // first instruction of an exception handler continuously double faults with a single cycle
    // memory access time) is sufficient that we'll only see a single bit set in the delay buffer.
    assign double_fault_seen_delay_buffer = {double_fault_seen_delay_buffer_q, double_fault_seen_o};

    always @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        double_fault_seen_delay_buffer_q <= '0;
        sync_exc_seen <= 1'b0;
      end else begin
        double_fault_seen_delay_buffer_q <=
          double_fault_seen_delay_buffer[DoubleFaultSeenLatency-2:0];

        if (new_sync_exc) begin
          // Set flag when we see a new synchronous exception
          sync_exc_seen <= 1'b1;
        end else if (rvfi_valid && rvfi_insn == 32'h30200073) begin
          // Clear flag when we see an MRET
          sync_exc_seen <= 1'b0;
        end else if (rvfi_valid && insn_write_sync_exc_seen(rvfi_insn)) begin
          // Update predicted sync_exc_seen when the instruction modifies the relevant CPUCTRLSTS
          // CSR bit.
          sync_exc_seen <= new_sync_exc_bit(rvfi_insn, rvfi_rs1_rdata, sync_exc_seen);
        end
      end
    end

    // We should only have a single assertion of double_fault_seen in the delay buffer
    `ASSERT(DoubleFaultSinglePulse, $onehot0(double_fault_seen_delay_buffer))
    // If we predict a double_fault_seen_o we should see one in the delay buffer
    `ASSERT(DoubleFaultPulseSeenOnDoubleFault,
      double_fault_seen_predicted |-> |double_fault_seen_delay_buffer)
    // If double_fault_seen_o is asserted we should see predict one occurring within a bounded time
    `ASSERT(DoubleFaultPulseOnlyOnDoubleFault,
      double_fault_seen_o |-> ##[0:DoubleFaultSeenLatency] double_fault_seen_predicted)
    `endif // RVFI
  `endif

  `ASSERT_KNOWN(IbexIrqX, {irq_software_i, irq_timer_i, irq_external_i, irq_fast_i, irq_nm_i})

  `ASSERT_KNOWN(IbexScrambleKeyValidX, scramble_key_valid_i)
  `ASSERT_KNOWN_IF(IbexScramblePayloadX, {scramble_key_i, scramble_nonce_i}, scramble_key_valid_i)

  `ASSERT_KNOWN(IbexDebugReqX, debug_req_i)
  `ASSERT_KNOWN(IbexFetchEnableX, fetch_enable_i)

  // Dummy instructions may only write to register 0, which is a special register when dummy
  // instructions are enabled.
  `ASSERT(WaddrAZeroForDummyInstr, dummy_instr_wb && rf_we_wb |-> rf_waddr_wb == '0)

  // Ensure the crash dump is connected to the correct internal signals
  `ASSERT(CrashDumpCurrentPCConn, crash_dump_o.current_pc === u_ibex_core.pc_id)
  `ASSERT(CrashDumpNextPCConn, crash_dump_o.next_pc === u_ibex_core.pc_if)
  `ASSERT(CrashDumpLastDataAddrConn,
    crash_dump_o.last_data_addr === u_ibex_core.load_store_unit_i.addr_last_q)
  `ASSERT(CrashDumpExceptionPCConn,
    crash_dump_o.exception_pc === u_ibex_core.cs_registers_i.mepc_q)
  `ASSERT(CrashDumpExceptionAddrConn,
    crash_dump_o.exception_addr === u_ibex_core.cs_registers_i.mtval_q)
endmodule
