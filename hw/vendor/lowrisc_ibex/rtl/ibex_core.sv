// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

`include "prim_assert.sv"
`include "dv_fcov_macros.svh"

/**
 * Top level module of the ibex RISC-V core
 */
module ibex_core import ibex_pkg::*; #(
  parameter bit          PMPEnable         = 1'b0,
  parameter int unsigned PMPGranularity    = 0,
  parameter int unsigned PMPNumRegions     = 4,
  parameter int unsigned MHPMCounterNum    = 0,
  parameter int unsigned MHPMCounterWidth  = 40,
  parameter bit          RV32E             = 1'b0,
  parameter rv32m_e      RV32M             = RV32MFast,
  parameter rv32b_e      RV32B             = RV32BNone,
  parameter bit          BranchTargetALU   = 1'b0,
  parameter bit          WritebackStage    = 1'b0,
  parameter bit          ICache            = 1'b0,
  parameter bit          ICacheECC         = 1'b0,
  parameter int unsigned BusSizeECC        = BUS_SIZE,
  parameter int unsigned TagSizeECC        = IC_TAG_SIZE,
  parameter int unsigned LineSizeECC       = IC_LINE_SIZE,
  parameter bit          BranchPredictor   = 1'b0,
  parameter bit          DbgTriggerEn      = 1'b0,
  parameter int unsigned DbgHwBreakNum     = 1,
  parameter bit          ResetAll          = 1'b0,
  parameter lfsr_seed_t  RndCnstLfsrSeed   = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t  RndCnstLfsrPerm   = RndCnstLfsrPermDefault,
  parameter bit          SecureIbex        = 1'b0,
  parameter bit          DummyInstructions = 1'b0,
  parameter bit          RegFileECC        = 1'b0,
  parameter int unsigned RegFileDataWidth  = 32,
  parameter bit          MemECC            = 1'b0,
  parameter int unsigned MemDataWidth      = MemECC ? 32 + 7 : 32,
  parameter int unsigned DmHaltAddr        = 32'h1A110800,
  parameter int unsigned DmExceptionAddr   = 32'h1A110808
) (
  // Clock and Reset
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,

  // Instruction memory interface
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  output logic [31:0]                  instr_addr_o,
  input  logic [MemDataWidth-1:0]      instr_rdata_i,
  input  logic                         instr_err_i,

  // Data memory interface
  output logic                         data_req_o,
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  output logic                         data_we_o,
  output logic [3:0]                   data_be_o,
  output logic [31:0]                  data_addr_o,
  output logic [MemDataWidth-1:0]      data_wdata_o,
  input  logic [MemDataWidth-1:0]      data_rdata_i,
  input  logic                         data_err_i,

  // Register file interface
  output logic                         dummy_instr_id_o,
  output logic [4:0]                   rf_raddr_a_o,
  output logic [4:0]                   rf_raddr_b_o,
  output logic [4:0]                   rf_waddr_wb_o,
  output logic                         rf_we_wb_o,
  output logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_o,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_i,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_i,

  // RAMs interface
  output logic [IC_NUM_WAYS-1:0]       ic_tag_req_o,
  output logic                         ic_tag_write_o,
  output logic [IC_INDEX_W-1:0]        ic_tag_addr_o,
  output logic [TagSizeECC-1:0]        ic_tag_wdata_o,
  input  logic [TagSizeECC-1:0]        ic_tag_rdata_i [IC_NUM_WAYS],
  output logic [IC_NUM_WAYS-1:0]       ic_data_req_o,
  output logic                         ic_data_write_o,
  output logic [IC_INDEX_W-1:0]        ic_data_addr_o,
  output logic [LineSizeECC-1:0]       ic_data_wdata_o,
  input  logic [LineSizeECC-1:0]       ic_data_rdata_i [IC_NUM_WAYS],
  input  logic                         ic_scr_key_valid_i,

  // Interrupt inputs
  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i,
  input  logic                         irq_nm_i,       // non-maskeable interrupt
  output logic                         irq_pending_o,

  // Debug Interface
  input  logic                         debug_req_i,
  output crash_dump_t                  crash_dump_o,
  // SEC_CM: EXCEPTION.CTRL_FLOW.LOCAL_ESC
  // SEC_CM: EXCEPTION.CTRL_FLOW.GLOBAL_ESC
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
  output logic                         rvfi_ext_debug_req,
  output logic [63:0]                  rvfi_ext_mcycle,
`endif

  // CPU Control Signals
  // SEC_CM: FETCH.CTRL.LC_GATED
  input  fetch_enable_t                fetch_enable_i,
  output logic                         alert_minor_o,
  output logic                         alert_major_internal_o,
  output logic                         alert_major_bus_o,
  output logic                         icache_inval_o,
  output logic                         core_busy_o
);

  localparam int unsigned PMP_NUM_CHAN      = 3;
  // SEC_CM: CORE.DATA_REG_SW.SCA
  localparam bit          DataIndTiming     = SecureIbex;
  localparam bit          PCIncrCheck       = SecureIbex;
  localparam bit          ShadowCSR         = 1'b0;

  // IF/ID signals
  logic        dummy_instr_id;
  logic        instr_valid_id;
  logic        instr_new_id;
  logic [31:0] instr_rdata_id;                 // Instruction sampled inside IF stage
  logic [31:0] instr_rdata_alu_id;             // Instruction sampled inside IF stage (replicated to
                                               // ease fan-out)
  logic [15:0] instr_rdata_c_id;               // Compressed instruction sampled inside IF stage
  logic        instr_is_compressed_id;
  logic        instr_perf_count_id;
  logic        instr_bp_taken_id;
  logic        instr_fetch_err;                // Bus error on instr fetch
  logic        instr_fetch_err_plus2;          // Instruction error is misaligned
  logic        illegal_c_insn_id;              // Illegal compressed instruction sent to ID stage
  logic [31:0] pc_if;                          // Program counter in IF stage
  logic [31:0] pc_id;                          // Program counter in ID stage
  logic [31:0] pc_wb;                          // Program counter in WB stage
  logic [33:0] imd_val_d_ex[2];                // Intermediate register for multicycle Ops
  logic [33:0] imd_val_q_ex[2];                // Intermediate register for multicycle Ops
  logic [1:0]  imd_val_we_ex;

  logic        data_ind_timing;
  logic        dummy_instr_en;
  logic [2:0]  dummy_instr_mask;
  logic        dummy_instr_seed_en;
  logic [31:0] dummy_instr_seed;
  logic        icache_enable;
  logic        icache_inval;
  logic        icache_ecc_error;
  logic        pc_mismatch_alert;
  logic        csr_shadow_err;

  logic        instr_first_cycle_id;
  logic        instr_valid_clear;
  logic        pc_set;
  logic        nt_branch_mispredict;
  logic [31:0] nt_branch_addr;
  pc_sel_e     pc_mux_id;                      // Mux selector for next PC
  exc_pc_sel_e exc_pc_mux_id;                  // Mux selector for exception PC
  exc_cause_t  exc_cause;                      // Exception cause

  logic        instr_intg_err;
  logic        lsu_load_err;
  logic        lsu_store_err;
  logic        lsu_load_intg_err;

  // LSU signals
  logic        lsu_addr_incr_req;
  logic [31:0] lsu_addr_last;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] branch_target_ex;
  logic        branch_decision;

  // Core busy signals
  logic        ctrl_busy;
  logic        if_busy;
  logic        lsu_busy;

  // Register File
  logic [4:0]  rf_raddr_a;
  logic [31:0] rf_rdata_a;
  logic [4:0]  rf_raddr_b;
  logic [31:0] rf_rdata_b;
  logic        rf_ren_a;
  logic        rf_ren_b;
  logic [4:0]  rf_waddr_wb;
  logic [31:0] rf_wdata_wb;
  // Writeback register write data that can be used on the forwarding path (doesn't factor in memory
  // read data as this is too late for the forwarding path)
  logic [31:0] rf_wdata_fwd_wb;
  logic [31:0] rf_wdata_lsu;
  logic        rf_we_wb;
  logic        rf_we_lsu;
  logic        rf_ecc_err_comb;

  logic [4:0]  rf_waddr_id;
  logic [31:0] rf_wdata_id;
  logic        rf_we_id;
  logic        rf_rd_a_wb_match;
  logic        rf_rd_b_wb_match;

  // ALU Control
  alu_op_e     alu_operator_ex;
  logic [31:0] alu_operand_a_ex;
  logic [31:0] alu_operand_b_ex;

  logic [31:0] bt_a_operand;
  logic [31:0] bt_b_operand;

  logic [31:0] alu_adder_result_ex;    // Used to forward computed address to LSU
  logic [31:0] result_ex;

  // Multiplier Control
  logic        mult_en_ex;
  logic        div_en_ex;
  logic        mult_sel_ex;
  logic        div_sel_ex;
  md_op_e      multdiv_operator_ex;
  logic [1:0]  multdiv_signed_mode_ex;
  logic [31:0] multdiv_operand_a_ex;
  logic [31:0] multdiv_operand_b_ex;
  logic        multdiv_ready_id;

  // CSR control
  logic        csr_access;
  csr_op_e     csr_op;
  logic        csr_op_en;
  csr_num_e    csr_addr;
  logic [31:0] csr_rdata;
  logic [31:0] csr_wdata;
  logic        illegal_csr_insn_id;    // CSR access to non-existent register,
                                       // with wrong priviledge level,
                                       // or missing write permissions

  // Data Memory Control
  logic        lsu_we;
  logic [1:0]  lsu_type;
  logic        lsu_sign_ext;
  logic        lsu_req;
  logic [31:0] lsu_wdata;
  logic        lsu_req_done;

  // stall control
  logic        id_in_ready;
  logic        ex_valid;

  logic        lsu_resp_valid;
  logic        lsu_resp_err;

  // Signals between instruction core interface and pipe (if and id stages)
  logic        instr_req_int;          // Id stage asserts a req to instruction core interface
  logic        instr_req_gated;

  // Writeback stage
  logic           en_wb;
  wb_instr_type_e instr_type_wb;
  logic           ready_wb;
  logic           rf_write_wb;
  logic           outstanding_load_wb;
  logic           outstanding_store_wb;

  // Interrupts
  logic        nmi_mode;
  irqs_t       irqs;
  logic        csr_mstatus_mie;
  logic [31:0] csr_mepc, csr_depc;

  // PMP signals
  logic [33:0]  csr_pmp_addr [PMPNumRegions];
  pmp_cfg_t     csr_pmp_cfg  [PMPNumRegions];
  pmp_mseccfg_t csr_pmp_mseccfg;
  logic         pmp_req_err  [PMP_NUM_CHAN];
  logic         data_req_out;

  logic        csr_save_if;
  logic        csr_save_id;
  logic        csr_save_wb;
  logic        csr_restore_mret_id;
  logic        csr_restore_dret_id;
  logic        csr_save_cause;
  logic        csr_mtvec_init;
  logic [31:0] csr_mtvec;
  logic [31:0] csr_mtval;
  logic        csr_mstatus_tw;
  priv_lvl_e   priv_mode_id;
  priv_lvl_e   priv_mode_lsu;

  // debug mode and dcsr configuration
  logic        debug_mode;
  dbg_cause_e  debug_cause;
  logic        debug_csr_save;
  logic        debug_single_step;
  logic        debug_ebreakm;
  logic        debug_ebreaku;
  logic        trigger_match;

  // signals relating to instruction movements between pipeline stages
  // used by performance counters and RVFI
  logic        instr_id_done;
  logic        instr_done_wb;

  logic        perf_instr_ret_wb;
  logic        perf_instr_ret_compressed_wb;
  logic        perf_instr_ret_wb_spec;
  logic        perf_instr_ret_compressed_wb_spec;
  logic        perf_iside_wait;
  logic        perf_dside_wait;
  logic        perf_mul_wait;
  logic        perf_div_wait;
  logic        perf_jump;
  logic        perf_branch;
  logic        perf_tbranch;
  logic        perf_load;
  logic        perf_store;

  // for RVFI
  logic        illegal_insn_id, unused_illegal_insn_id; // ID stage sees an illegal instruction

  //////////////////////
  // Clock management //
  //////////////////////

  // Before going to sleep, wait for I- and D-side
  // interfaces to finish ongoing operations.
  assign core_busy_o = ctrl_busy | if_busy | lsu_busy;

  //////////////
  // IF stage //
  //////////////

  ibex_if_stage #(
    .DmHaltAddr       (DmHaltAddr),
    .DmExceptionAddr  (DmExceptionAddr),
    .DummyInstructions(DummyInstructions),
    .ICache           (ICache),
    .ICacheECC        (ICacheECC),
    .BusSizeECC       (BusSizeECC),
    .TagSizeECC       (TagSizeECC),
    .LineSizeECC      (LineSizeECC),
    .PCIncrCheck      (PCIncrCheck),
    .ResetAll         (ResetAll),
    .RndCnstLfsrSeed  (RndCnstLfsrSeed),
    .RndCnstLfsrPerm  (RndCnstLfsrPerm),
    .BranchPredictor  (BranchPredictor),
    .MemECC           (MemECC),
    .MemDataWidth     (MemDataWidth)
  ) if_stage_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .boot_addr_i(boot_addr_i),
    .req_i      (instr_req_gated),  // instruction request control

    // instruction cache interface
    .instr_req_o       (instr_req_o),
    .instr_addr_o      (instr_addr_o),
    .instr_gnt_i       (instr_gnt_i),
    .instr_rvalid_i    (instr_rvalid_i),
    .instr_rdata_i     (instr_rdata_i),
    .instr_bus_err_i   (instr_err_i),
    .instr_intg_err_o  (instr_intg_err),

    .ic_tag_req_o      (ic_tag_req_o),
    .ic_tag_write_o    (ic_tag_write_o),
    .ic_tag_addr_o     (ic_tag_addr_o),
    .ic_tag_wdata_o    (ic_tag_wdata_o),
    .ic_tag_rdata_i    (ic_tag_rdata_i),
    .ic_data_req_o     (ic_data_req_o),
    .ic_data_write_o   (ic_data_write_o),
    .ic_data_addr_o    (ic_data_addr_o),
    .ic_data_wdata_o   (ic_data_wdata_o),
    .ic_data_rdata_i   (ic_data_rdata_i),
    .ic_scr_key_valid_i(ic_scr_key_valid_i),

    // outputs to ID stage
    .instr_valid_id_o        (instr_valid_id),
    .instr_new_id_o          (instr_new_id),
    .instr_rdata_id_o        (instr_rdata_id),
    .instr_rdata_alu_id_o    (instr_rdata_alu_id),
    .instr_rdata_c_id_o      (instr_rdata_c_id),
    .instr_is_compressed_id_o(instr_is_compressed_id),
    .instr_bp_taken_o        (instr_bp_taken_id),
    .instr_fetch_err_o       (instr_fetch_err),
    .instr_fetch_err_plus2_o (instr_fetch_err_plus2),
    .illegal_c_insn_id_o     (illegal_c_insn_id),
    .dummy_instr_id_o        (dummy_instr_id),
    .pc_if_o                 (pc_if),
    .pc_id_o                 (pc_id),
    .pmp_err_if_i            (pmp_req_err[PMP_I]),
    .pmp_err_if_plus2_i      (pmp_req_err[PMP_I2]),

    // control signals
    .instr_valid_clear_i   (instr_valid_clear),
    .pc_set_i              (pc_set),
    .pc_mux_i              (pc_mux_id),
    .nt_branch_mispredict_i(nt_branch_mispredict),
    .exc_pc_mux_i          (exc_pc_mux_id),
    .exc_cause             (exc_cause),
    .dummy_instr_en_i      (dummy_instr_en),
    .dummy_instr_mask_i    (dummy_instr_mask),
    .dummy_instr_seed_en_i (dummy_instr_seed_en),
    .dummy_instr_seed_i    (dummy_instr_seed),
    .icache_enable_i       (icache_enable),
    .icache_inval_i        (icache_inval),
    .icache_ecc_error_o    (icache_ecc_error),

    // branch targets
    .branch_target_ex_i(branch_target_ex),
    .nt_branch_addr_i  (nt_branch_addr),

    // CSRs
    .csr_mepc_i      (csr_mepc),  // exception return address
    .csr_depc_i      (csr_depc),  // debug return address
    .csr_mtvec_i     (csr_mtvec),  // trap-vector base address
    .csr_mtvec_init_o(csr_mtvec_init),

    // pipeline stalls
    .id_in_ready_i(id_in_ready),

    .pc_mismatch_alert_o(pc_mismatch_alert),
    .if_busy_o          (if_busy)
  );

  // Core is waiting for the ISide when ID/EX stage is ready for a new instruction but none are
  // available
  assign perf_iside_wait = id_in_ready & ~instr_valid_id;

  // Multi-bit fetch enable used when SecureIbex == 1. When SecureIbex == 0 only use the bottom-bit
  // of fetch_enable_i. Ensure the multi-bit encoding has the bottom bit set for on and unset for
  // off so FetchEnableOn/FetchEnableOff can be used without needing to know the value of
  // SecureIbex.
  `ASSERT_INIT(FetchEnableSecureOnBottomBitSet,    FetchEnableOn[0] == 1'b1)
  `ASSERT_INIT(FetchEnableSecureOffBottomBitClear, FetchEnableOff[0] == 1'b0)

  // fetch_enable_i can be used to stop the core fetching new instructions
  if (SecureIbex) begin : g_instr_req_gated_secure
    // For secure Ibex fetch_enable_i must be a specific multi-bit pattern to enable instruction
    // fetch
    // SEC_CM: FETCH.CTRL.LC_GATED
    assign instr_req_gated = instr_req_int & (fetch_enable_i == FetchEnableOn);
  end else begin : g_instr_req_gated_non_secure
    // For non secure Ibex only the bottom bit of fetch enable is considered
    logic unused_fetch_enable;
    assign unused_fetch_enable = ^fetch_enable_i[$bits(fetch_enable_t)-1:1];

    assign instr_req_gated = instr_req_int & fetch_enable_i[0];
  end

  //////////////
  // ID stage //
  //////////////

  ibex_id_stage #(
    .RV32E          (RV32E),
    .RV32M          (RV32M),
    .RV32B          (RV32B),
    .BranchTargetALU(BranchTargetALU),
    .DataIndTiming  (DataIndTiming),
    .WritebackStage (WritebackStage),
    .BranchPredictor(BranchPredictor),
    .MemECC         (MemECC)
  ) id_stage_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // Processor Enable
    .ctrl_busy_o   (ctrl_busy),
    .illegal_insn_o(illegal_insn_id),

    // from/to IF-ID pipeline register
    .instr_valid_i        (instr_valid_id),
    .instr_rdata_i        (instr_rdata_id),
    .instr_rdata_alu_i    (instr_rdata_alu_id),
    .instr_rdata_c_i      (instr_rdata_c_id),
    .instr_is_compressed_i(instr_is_compressed_id),
    .instr_bp_taken_i     (instr_bp_taken_id),

    // Jumps and branches
    .branch_decision_i(branch_decision),

    // IF and ID control signals
    .instr_first_cycle_id_o(instr_first_cycle_id),
    .instr_valid_clear_o   (instr_valid_clear),
    .id_in_ready_o         (id_in_ready),
    .instr_req_o           (instr_req_int),
    .pc_set_o              (pc_set),
    .pc_mux_o              (pc_mux_id),
    .nt_branch_mispredict_o(nt_branch_mispredict),
    .nt_branch_addr_o      (nt_branch_addr),
    .exc_pc_mux_o          (exc_pc_mux_id),
    .exc_cause_o           (exc_cause),
    .icache_inval_o        (icache_inval),

    .instr_fetch_err_i      (instr_fetch_err),
    .instr_fetch_err_plus2_i(instr_fetch_err_plus2),
    .illegal_c_insn_i       (illegal_c_insn_id),

    .pc_id_i(pc_id),

    // Stalls
    .ex_valid_i      (ex_valid),
    .lsu_resp_valid_i(lsu_resp_valid),

    .alu_operator_ex_o (alu_operator_ex),
    .alu_operand_a_ex_o(alu_operand_a_ex),
    .alu_operand_b_ex_o(alu_operand_b_ex),

    .imd_val_q_ex_o (imd_val_q_ex),
    .imd_val_d_ex_i (imd_val_d_ex),
    .imd_val_we_ex_i(imd_val_we_ex),

    .bt_a_operand_o(bt_a_operand),
    .bt_b_operand_o(bt_b_operand),

    .mult_en_ex_o            (mult_en_ex),
    .div_en_ex_o             (div_en_ex),
    .mult_sel_ex_o           (mult_sel_ex),
    .div_sel_ex_o            (div_sel_ex),
    .multdiv_operator_ex_o   (multdiv_operator_ex),
    .multdiv_signed_mode_ex_o(multdiv_signed_mode_ex),
    .multdiv_operand_a_ex_o  (multdiv_operand_a_ex),
    .multdiv_operand_b_ex_o  (multdiv_operand_b_ex),
    .multdiv_ready_id_o      (multdiv_ready_id),

    // CSR ID/EX
    .csr_access_o         (csr_access),
    .csr_op_o             (csr_op),
    .csr_op_en_o          (csr_op_en),
    .csr_save_if_o        (csr_save_if),  // control signal to save PC
    .csr_save_id_o        (csr_save_id),  // control signal to save PC
    .csr_save_wb_o        (csr_save_wb),  // control signal to save PC
    .csr_restore_mret_id_o(csr_restore_mret_id),  // restore mstatus upon MRET
    .csr_restore_dret_id_o(csr_restore_dret_id),  // restore mstatus upon MRET
    .csr_save_cause_o     (csr_save_cause),
    .csr_mtval_o          (csr_mtval),
    .priv_mode_i          (priv_mode_id),
    .csr_mstatus_tw_i     (csr_mstatus_tw),
    .illegal_csr_insn_i   (illegal_csr_insn_id),
    .data_ind_timing_i    (data_ind_timing),

    // LSU
    .lsu_req_o     (lsu_req),  // to load store unit
    .lsu_we_o      (lsu_we),  // to load store unit
    .lsu_type_o    (lsu_type),  // to load store unit
    .lsu_sign_ext_o(lsu_sign_ext),  // to load store unit
    .lsu_wdata_o   (lsu_wdata),  // to load store unit
    .lsu_req_done_i(lsu_req_done),  // from load store unit

    .lsu_addr_incr_req_i(lsu_addr_incr_req),
    .lsu_addr_last_i    (lsu_addr_last),

    .lsu_load_err_i     (lsu_load_err),
    .lsu_load_intg_err_i(lsu_load_intg_err),
    .lsu_store_err_i    (lsu_store_err),

    // Interrupt Signals
    .csr_mstatus_mie_i(csr_mstatus_mie),
    .irq_pending_i    (irq_pending_o),
    .irqs_i           (irqs),
    .irq_nm_i         (irq_nm_i),
    .nmi_mode_o       (nmi_mode),

    // Debug Signal
    .debug_mode_o       (debug_mode),
    .debug_cause_o      (debug_cause),
    .debug_csr_save_o   (debug_csr_save),
    .debug_req_i        (debug_req_i),
    .debug_single_step_i(debug_single_step),
    .debug_ebreakm_i    (debug_ebreakm),
    .debug_ebreaku_i    (debug_ebreaku),
    .trigger_match_i    (trigger_match),

    // write data to commit in the register file
    .result_ex_i(result_ex),
    .csr_rdata_i(csr_rdata),

    .rf_raddr_a_o      (rf_raddr_a),
    .rf_rdata_a_i      (rf_rdata_a),
    .rf_raddr_b_o      (rf_raddr_b),
    .rf_rdata_b_i      (rf_rdata_b),
    .rf_ren_a_o        (rf_ren_a),
    .rf_ren_b_o        (rf_ren_b),
    .rf_waddr_id_o     (rf_waddr_id),
    .rf_wdata_id_o     (rf_wdata_id),
    .rf_we_id_o        (rf_we_id),
    .rf_rd_a_wb_match_o(rf_rd_a_wb_match),
    .rf_rd_b_wb_match_o(rf_rd_b_wb_match),

    .rf_waddr_wb_i    (rf_waddr_wb),
    .rf_wdata_fwd_wb_i(rf_wdata_fwd_wb),
    .rf_write_wb_i    (rf_write_wb),

    .en_wb_o               (en_wb),
    .instr_type_wb_o       (instr_type_wb),
    .instr_perf_count_id_o (instr_perf_count_id),
    .ready_wb_i            (ready_wb),
    .outstanding_load_wb_i (outstanding_load_wb),
    .outstanding_store_wb_i(outstanding_store_wb),

    // Performance Counters
    .perf_jump_o      (perf_jump),
    .perf_branch_o    (perf_branch),
    .perf_tbranch_o   (perf_tbranch),
    .perf_dside_wait_o(perf_dside_wait),
    .perf_mul_wait_o  (perf_mul_wait),
    .perf_div_wait_o  (perf_div_wait),
    .instr_id_done_o  (instr_id_done)
  );

  assign icache_inval_o = icache_inval;
  // for RVFI only
  assign unused_illegal_insn_id = illegal_insn_id;

  ibex_ex_block #(
    .RV32M          (RV32M),
    .RV32B          (RV32B),
    .BranchTargetALU(BranchTargetALU)
  ) ex_block_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // ALU signal from ID stage
    .alu_operator_i         (alu_operator_ex),
    .alu_operand_a_i        (alu_operand_a_ex),
    .alu_operand_b_i        (alu_operand_b_ex),
    .alu_instr_first_cycle_i(instr_first_cycle_id),

    // Branch target ALU signal from ID stage
    .bt_a_operand_i(bt_a_operand),
    .bt_b_operand_i(bt_b_operand),

    // Multipler/Divider signal from ID stage
    .multdiv_operator_i   (multdiv_operator_ex),
    .mult_en_i            (mult_en_ex),
    .div_en_i             (div_en_ex),
    .mult_sel_i           (mult_sel_ex),
    .div_sel_i            (div_sel_ex),
    .multdiv_signed_mode_i(multdiv_signed_mode_ex),
    .multdiv_operand_a_i  (multdiv_operand_a_ex),
    .multdiv_operand_b_i  (multdiv_operand_b_ex),
    .multdiv_ready_id_i   (multdiv_ready_id),
    .data_ind_timing_i    (data_ind_timing),

    // Intermediate value register
    .imd_val_we_o(imd_val_we_ex),
    .imd_val_d_o (imd_val_d_ex),
    .imd_val_q_i (imd_val_q_ex),

    // Outputs
    .alu_adder_result_ex_o(alu_adder_result_ex),  // to LSU
    .result_ex_o          (result_ex),  // to ID

    .branch_target_o  (branch_target_ex),  // to IF
    .branch_decision_o(branch_decision),  // to ID

    .ex_valid_o(ex_valid)
  );

  /////////////////////
  // Load/store unit //
  /////////////////////

  assign data_req_o   = data_req_out & ~pmp_req_err[PMP_D];
  assign lsu_resp_err = lsu_load_err | lsu_store_err;

  ibex_load_store_unit #(
    .MemECC(MemECC),
    .MemDataWidth(MemDataWidth)
  ) load_store_unit_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // data interface
    .data_req_o    (data_req_out),
    .data_gnt_i    (data_gnt_i),
    .data_rvalid_i (data_rvalid_i),
    .data_bus_err_i(data_err_i),
    .data_pmp_err_i(pmp_req_err[PMP_D]),

    .data_addr_o      (data_addr_o),
    .data_we_o        (data_we_o),
    .data_be_o        (data_be_o),
    .data_wdata_o     (data_wdata_o),
    .data_rdata_i     (data_rdata_i),

    // signals to/from ID/EX stage
    .lsu_we_i      (lsu_we),
    .lsu_type_i    (lsu_type),
    .lsu_wdata_i   (lsu_wdata),
    .lsu_sign_ext_i(lsu_sign_ext),

    .lsu_rdata_o      (rf_wdata_lsu),
    .lsu_rdata_valid_o(rf_we_lsu),
    .lsu_req_i        (lsu_req),
    .lsu_req_done_o   (lsu_req_done),

    .adder_result_ex_i(alu_adder_result_ex),

    .addr_incr_req_o(lsu_addr_incr_req),
    .addr_last_o    (lsu_addr_last),


    .lsu_resp_valid_o(lsu_resp_valid),

    // exception signals
    .load_err_o     (lsu_load_err),
    .store_err_o    (lsu_store_err),
    .load_intg_err_o(lsu_load_intg_err),

    .busy_o(lsu_busy),

    .perf_load_o (perf_load),
    .perf_store_o(perf_store)
  );

  ibex_wb_stage #(
    .ResetAll       ( ResetAll       ),
    .WritebackStage(WritebackStage)
  ) wb_stage_i (
    .clk_i                   (clk_i),
    .rst_ni                  (rst_ni),
    .en_wb_i                 (en_wb),
    .instr_type_wb_i         (instr_type_wb),
    .pc_id_i                 (pc_id),
    .instr_is_compressed_id_i(instr_is_compressed_id),
    .instr_perf_count_id_i   (instr_perf_count_id),

    .ready_wb_o                         (ready_wb),
    .rf_write_wb_o                      (rf_write_wb),
    .outstanding_load_wb_o              (outstanding_load_wb),
    .outstanding_store_wb_o             (outstanding_store_wb),
    .pc_wb_o                            (pc_wb),
    .perf_instr_ret_wb_o                (perf_instr_ret_wb),
    .perf_instr_ret_compressed_wb_o     (perf_instr_ret_compressed_wb),
    .perf_instr_ret_wb_spec_o           (perf_instr_ret_wb_spec),
    .perf_instr_ret_compressed_wb_spec_o(perf_instr_ret_compressed_wb_spec),

    .rf_waddr_id_i(rf_waddr_id),
    .rf_wdata_id_i(rf_wdata_id),
    .rf_we_id_i   (rf_we_id),

    .rf_wdata_lsu_i(rf_wdata_lsu),
    .rf_we_lsu_i   (rf_we_lsu),

    .rf_wdata_fwd_wb_o(rf_wdata_fwd_wb),

    .rf_waddr_wb_o(rf_waddr_wb),
    .rf_wdata_wb_o(rf_wdata_wb),
    .rf_we_wb_o   (rf_we_wb),

    .lsu_resp_valid_i(lsu_resp_valid),
    .lsu_resp_err_i  (lsu_resp_err),

    .instr_done_wb_o(instr_done_wb)
  );

  /////////////////////////////
  // Register file interface //
  /////////////////////////////

  assign dummy_instr_id_o = dummy_instr_id;
  assign rf_raddr_a_o     = rf_raddr_a;
  assign rf_waddr_wb_o    = rf_waddr_wb;
  assign rf_we_wb_o       = rf_we_wb;
  assign rf_raddr_b_o     = rf_raddr_b;

  if (RegFileECC) begin : gen_regfile_ecc

    // SEC_CM: DATA_REG_SW.INTEGRITY
    logic [1:0] rf_ecc_err_a, rf_ecc_err_b;
    logic       rf_ecc_err_a_id, rf_ecc_err_b_id;

    // ECC checkbit generation for regiter file wdata
    prim_secded_inv_39_32_enc regfile_ecc_enc (
      .data_i(rf_wdata_wb),
      .data_o(rf_wdata_wb_ecc_o)
    );

    // ECC checking on register file rdata
    prim_secded_inv_39_32_dec regfile_ecc_dec_a (
      .data_i    (rf_rdata_a_ecc_i),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rf_ecc_err_a)
    );
    prim_secded_inv_39_32_dec regfile_ecc_dec_b (
      .data_i    (rf_rdata_b_ecc_i),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rf_ecc_err_b)
    );

    // Assign read outputs - no error correction, just trigger an alert
    assign rf_rdata_a = rf_rdata_a_ecc_i[31:0];
    assign rf_rdata_b = rf_rdata_b_ecc_i[31:0];

    // Calculate errors - qualify with WB forwarding to avoid xprop into the alert signal
    assign rf_ecc_err_a_id = |rf_ecc_err_a & rf_ren_a & ~rf_rd_a_wb_match;
    assign rf_ecc_err_b_id = |rf_ecc_err_b & rf_ren_b & ~rf_rd_b_wb_match;

    // Combined error
    assign rf_ecc_err_comb = instr_valid_id & (rf_ecc_err_a_id | rf_ecc_err_b_id);

  end else begin : gen_no_regfile_ecc
    logic unused_rf_ren_a, unused_rf_ren_b;
    logic unused_rf_rd_a_wb_match, unused_rf_rd_b_wb_match;

    assign unused_rf_ren_a         = rf_ren_a;
    assign unused_rf_ren_b         = rf_ren_b;
    assign unused_rf_rd_a_wb_match = rf_rd_a_wb_match;
    assign unused_rf_rd_b_wb_match = rf_rd_b_wb_match;
    assign rf_wdata_wb_ecc_o       = rf_wdata_wb;
    assign rf_rdata_a              = rf_rdata_a_ecc_i;
    assign rf_rdata_b              = rf_rdata_b_ecc_i;
    assign rf_ecc_err_comb         = 1'b0;
  end

  ///////////////////////
  // Crash dump output //
  ///////////////////////

  assign crash_dump_o.current_pc     = pc_id;
  assign crash_dump_o.next_pc        = pc_if;
  assign crash_dump_o.last_data_addr = lsu_addr_last;
  assign crash_dump_o.exception_addr = csr_mepc;

  ///////////////////
  // Alert outputs //
  ///////////////////

  // Minor alert - core is in a recoverable state
  assign alert_minor_o = icache_ecc_error;

  // Major internal alert - core is unrecoverable
  assign alert_major_internal_o = rf_ecc_err_comb | pc_mismatch_alert | csr_shadow_err;
  // Major bus alert
  assign alert_major_bus_o = lsu_load_intg_err | instr_intg_err;

  // Explict INC_ASSERT block to avoid unused signal lint warnings were asserts are not included
  `ifdef INC_ASSERT
  // Signals used for assertions only
  logic outstanding_load_resp;
  logic outstanding_store_resp;

  logic outstanding_load_id;
  logic outstanding_store_id;

  assign outstanding_load_id  = id_stage_i.instr_executing & id_stage_i.lsu_req_dec &
                                ~id_stage_i.lsu_we;
  assign outstanding_store_id = id_stage_i.instr_executing & id_stage_i.lsu_req_dec &
                                id_stage_i.lsu_we;

  if (WritebackStage) begin : gen_wb_stage
    // When the writeback stage is present a load/store could be in ID or WB. A Load/store in ID can
    // see a response before it moves to WB when it is unaligned otherwise we should only see
    // a response when load/store is in WB.
    assign outstanding_load_resp  = outstanding_load_wb |
      (outstanding_load_id  & load_store_unit_i.split_misaligned_access);

    assign outstanding_store_resp = outstanding_store_wb |
      (outstanding_store_id & load_store_unit_i.split_misaligned_access);

    // When writing back the result of a load, the load must have made it to writeback
    `ASSERT(NoMemRFWriteWithoutPendingLoad, rf_we_lsu |-> outstanding_load_wb, clk_i, !rst_ni)
  end else begin : gen_no_wb_stage
    // Without writeback stage only look into whether load or store is in ID to determine if
    // a response is expected.
    assign outstanding_load_resp  = outstanding_load_id;
    assign outstanding_store_resp = outstanding_store_id;

    `ASSERT(NoMemRFWriteWithoutPendingLoad, rf_we_lsu |-> outstanding_load_id, clk_i, !rst_ni)
  end

  `ASSERT(NoMemResponseWithoutPendingAccess,
    data_rvalid_i |-> outstanding_load_resp | outstanding_store_resp, clk_i, !rst_ni)
  `endif

  ////////////////////////
  // RF (Register File) //
  ////////////////////////
`ifdef RVFI
`endif


  /////////////////////////////////////////
  // CSRs (Control and Status Registers) //
  /////////////////////////////////////////

  assign csr_wdata  = alu_operand_a_ex;
  assign csr_addr   = csr_num_e'(csr_access ? alu_operand_b_ex[11:0] : 12'b0);

  ibex_cs_registers #(
    .DbgTriggerEn     (DbgTriggerEn),
    .DbgHwBreakNum    (DbgHwBreakNum),
    .DataIndTiming    (DataIndTiming),
    .DummyInstructions(DummyInstructions),
    .ShadowCSR        (ShadowCSR),
    .ICache           (ICache),
    .MHPMCounterNum   (MHPMCounterNum),
    .MHPMCounterWidth (MHPMCounterWidth),
    .PMPEnable        (PMPEnable),
    .PMPGranularity   (PMPGranularity),
    .PMPNumRegions    (PMPNumRegions),
    .RV32E            (RV32E),
    .RV32M            (RV32M),
    .RV32B            (RV32B)
  ) cs_registers_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // Hart ID from outside
    .hart_id_i      (hart_id_i),
    .priv_mode_id_o (priv_mode_id),
    .priv_mode_lsu_o(priv_mode_lsu),

    // mtvec
    .csr_mtvec_o     (csr_mtvec),
    .csr_mtvec_init_i(csr_mtvec_init),
    .boot_addr_i     (boot_addr_i),

    // Interface to CSRs     ( SRAM like                    )
    .csr_access_i(csr_access),
    .csr_addr_i  (csr_addr),
    .csr_wdata_i (csr_wdata),
    .csr_op_i    (csr_op),
    .csr_op_en_i (csr_op_en),
    .csr_rdata_o (csr_rdata),

    // Interrupt related control signals
    .irq_software_i   (irq_software_i),
    .irq_timer_i      (irq_timer_i),
    .irq_external_i   (irq_external_i),
    .irq_fast_i       (irq_fast_i),
    .nmi_mode_i       (nmi_mode),
    .irq_pending_o    (irq_pending_o),
    .irqs_o           (irqs),
    .csr_mstatus_mie_o(csr_mstatus_mie),
    .csr_mstatus_tw_o (csr_mstatus_tw),
    .csr_mepc_o       (csr_mepc),

    // PMP
    .csr_pmp_cfg_o    (csr_pmp_cfg),
    .csr_pmp_addr_o   (csr_pmp_addr),
    .csr_pmp_mseccfg_o(csr_pmp_mseccfg),

    // debug
    .csr_depc_o         (csr_depc),
    .debug_mode_i       (debug_mode),
    .debug_cause_i      (debug_cause),
    .debug_csr_save_i   (debug_csr_save),
    .debug_single_step_o(debug_single_step),
    .debug_ebreakm_o    (debug_ebreakm),
    .debug_ebreaku_o    (debug_ebreaku),
    .trigger_match_o    (trigger_match),

    .pc_if_i(pc_if),
    .pc_id_i(pc_id),
    .pc_wb_i(pc_wb),

    .data_ind_timing_o    (data_ind_timing),
    .dummy_instr_en_o     (dummy_instr_en),
    .dummy_instr_mask_o   (dummy_instr_mask),
    .dummy_instr_seed_en_o(dummy_instr_seed_en),
    .dummy_instr_seed_o   (dummy_instr_seed),
    .icache_enable_o      (icache_enable),
    .csr_shadow_err_o     (csr_shadow_err),

    .csr_save_if_i     (csr_save_if),
    .csr_save_id_i     (csr_save_id),
    .csr_save_wb_i     (csr_save_wb),
    .csr_restore_mret_i(csr_restore_mret_id),
    .csr_restore_dret_i(csr_restore_dret_id),
    .csr_save_cause_i  (csr_save_cause),
    .csr_mcause_i      (exc_cause),
    .csr_mtval_i       (csr_mtval),
    .illegal_csr_insn_o(illegal_csr_insn_id),

    .double_fault_seen_o,

    // performance counter related signals
    .instr_ret_i                (perf_instr_ret_wb),
    .instr_ret_compressed_i     (perf_instr_ret_compressed_wb),
    .instr_ret_spec_i           (perf_instr_ret_wb_spec),
    .instr_ret_compressed_spec_i(perf_instr_ret_compressed_wb_spec),
    .iside_wait_i               (perf_iside_wait),
    .jump_i                     (perf_jump),
    .branch_i                   (perf_branch),
    .branch_taken_i             (perf_tbranch),
    .mem_load_i                 (perf_load),
    .mem_store_i                (perf_store),
    .dside_wait_i               (perf_dside_wait),
    .mul_wait_i                 (perf_mul_wait),
    .div_wait_i                 (perf_div_wait)
  );

  // These assertions are in top-level as instr_valid_id required as the enable term
  `ASSERT(IbexCsrOpValid, instr_valid_id |-> csr_op inside {
      CSR_OP_READ,
      CSR_OP_WRITE,
      CSR_OP_SET,
      CSR_OP_CLEAR
      })
  `ASSERT_KNOWN_IF(IbexCsrWdataIntKnown, cs_registers_i.csr_wdata_int, csr_op_en)

  if (PMPEnable) begin : g_pmp
    logic [33:0] pmp_req_addr [PMP_NUM_CHAN];
    pmp_req_e    pmp_req_type [PMP_NUM_CHAN];
    priv_lvl_e   pmp_priv_lvl [PMP_NUM_CHAN];

    assign pmp_req_addr[PMP_I]  = {2'b00, pc_if};
    assign pmp_req_type[PMP_I]  = PMP_ACC_EXEC;
    assign pmp_priv_lvl[PMP_I]  = priv_mode_id;
    assign pmp_req_addr[PMP_I2] = {2'b00, (pc_if + 32'd2)};
    assign pmp_req_type[PMP_I2] = PMP_ACC_EXEC;
    assign pmp_priv_lvl[PMP_I2] = priv_mode_id;
    assign pmp_req_addr[PMP_D]  = {2'b00, data_addr_o[31:0]};
    assign pmp_req_type[PMP_D]  = data_we_o ? PMP_ACC_WRITE : PMP_ACC_READ;
    assign pmp_priv_lvl[PMP_D]  = priv_mode_lsu;

    ibex_pmp #(
      .PMPGranularity(PMPGranularity),
      .PMPNumChan    (PMP_NUM_CHAN),
      .PMPNumRegions (PMPNumRegions)
    ) pmp_i (
      .clk_i            (clk_i),
      .rst_ni           (rst_ni),
      // Interface to CSRs
      .csr_pmp_cfg_i    (csr_pmp_cfg),
      .csr_pmp_addr_i   (csr_pmp_addr),
      .csr_pmp_mseccfg_i(csr_pmp_mseccfg),
      .priv_mode_i      (pmp_priv_lvl),
      // Access checking channels
      .pmp_req_addr_i   (pmp_req_addr),
      .pmp_req_type_i   (pmp_req_type),
      .pmp_req_err_o    (pmp_req_err)
    );
  end else begin : g_no_pmp
    // Unused signal tieoff
    priv_lvl_e unused_priv_lvl_ls;
    logic [33:0] unused_csr_pmp_addr [PMPNumRegions];
    pmp_cfg_t    unused_csr_pmp_cfg  [PMPNumRegions];
    pmp_mseccfg_t unused_csr_pmp_mseccfg;
    assign unused_priv_lvl_ls = priv_mode_lsu;
    assign unused_csr_pmp_addr = csr_pmp_addr;
    assign unused_csr_pmp_cfg = csr_pmp_cfg;
    assign unused_csr_pmp_mseccfg = csr_pmp_mseccfg;

    // Output tieoff
    assign pmp_req_err[PMP_I]  = 1'b0;
    assign pmp_req_err[PMP_I2] = 1'b0;
    assign pmp_req_err[PMP_D]  = 1'b0;
  end

`ifdef RVFI
  // When writeback stage is present RVFI information is emitted when instruction is finished in
  // third stage but some information must be captured whilst the instruction is in the second
  // stage. Without writeback stage RVFI information is all emitted when instruction retires in
  // second stage. RVFI outputs are all straight from flops. So 2 stage pipeline requires a single
  // set of flops (instr_info => RVFI_out), 3 stage pipeline requires two sets (instr_info => wb
  // => RVFI_out)
  localparam int RVFI_STAGES = WritebackStage ? 2 : 1;

  logic        rvfi_stage_valid     [RVFI_STAGES];
  logic [63:0] rvfi_stage_order     [RVFI_STAGES];
  logic [31:0] rvfi_stage_insn      [RVFI_STAGES];
  logic        rvfi_stage_trap      [RVFI_STAGES];
  logic        rvfi_stage_halt      [RVFI_STAGES];
  logic        rvfi_stage_intr      [RVFI_STAGES];
  logic [ 1:0] rvfi_stage_mode      [RVFI_STAGES];
  logic [ 1:0] rvfi_stage_ixl       [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs1_addr  [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs2_addr  [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs3_addr  [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs1_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs2_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs3_rdata [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rd_addr   [RVFI_STAGES];
  logic [31:0] rvfi_stage_rd_wdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_pc_rdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_pc_wdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_addr  [RVFI_STAGES];
  logic [ 3:0] rvfi_stage_mem_rmask [RVFI_STAGES];
  logic [ 3:0] rvfi_stage_mem_wmask [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_wdata [RVFI_STAGES];

  logic        rvfi_instr_new_wb;
  logic        rvfi_intr_d;
  logic        rvfi_intr_q;
  logic        rvfi_set_trap_pc_d;
  logic        rvfi_set_trap_pc_q;
  logic [31:0] rvfi_insn_id;
  logic [4:0]  rvfi_rs1_addr_d;
  logic [4:0]  rvfi_rs1_addr_q;
  logic [4:0]  rvfi_rs2_addr_d;
  logic [4:0]  rvfi_rs2_addr_q;
  logic [4:0]  rvfi_rs3_addr_d;
  logic [31:0] rvfi_rs1_data_d;
  logic [31:0] rvfi_rs1_data_q;
  logic [31:0] rvfi_rs2_data_d;
  logic [31:0] rvfi_rs2_data_q;
  logic [31:0] rvfi_rs3_data_d;
  logic [4:0]  rvfi_rd_addr_wb;
  logic [4:0]  rvfi_rd_addr_q;
  logic [4:0]  rvfi_rd_addr_d;
  logic [31:0] rvfi_rd_wdata_wb;
  logic [31:0] rvfi_rd_wdata_d;
  logic [31:0] rvfi_rd_wdata_q;
  logic        rvfi_rd_we_wb;
  logic [3:0]  rvfi_mem_mask_int;
  logic [31:0] rvfi_mem_rdata_d;
  logic [31:0] rvfi_mem_rdata_q;
  logic [31:0] rvfi_mem_wdata_d;
  logic [31:0] rvfi_mem_wdata_q;
  logic [31:0] rvfi_mem_addr_d;
  logic [31:0] rvfi_mem_addr_q;
  logic        rvfi_trap_id;
  logic        rvfi_trap_wb;
  logic [63:0] rvfi_stage_order_d;
  logic        rvfi_id_done;
  logic        rvfi_wb_done;

  logic            new_debug_req;
  logic            new_nmi;
  logic            new_irq;
  ibex_pkg::irqs_t captured_mip;
  logic            captured_nmi;
  logic            captured_debug_req;
  logic            captured_valid;

  // RVFI extension for co-simulation support
  // debug_req and MIP captured at IF -> ID transition so one extra stage
  ibex_pkg::irqs_t rvfi_ext_stage_mip          [RVFI_STAGES+1];
  logic            rvfi_ext_stage_nmi          [RVFI_STAGES+1];
  logic            rvfi_ext_stage_debug_req    [RVFI_STAGES+1];
  logic [63:0]     rvfi_ext_stage_mcycle       [RVFI_STAGES];



  logic        rvfi_stage_valid_d   [RVFI_STAGES];

  assign rvfi_valid     = rvfi_stage_valid    [RVFI_STAGES-1];
  assign rvfi_order     = rvfi_stage_order    [RVFI_STAGES-1];
  assign rvfi_insn      = rvfi_stage_insn     [RVFI_STAGES-1];
  assign rvfi_trap      = rvfi_stage_trap     [RVFI_STAGES-1];
  assign rvfi_halt      = rvfi_stage_halt     [RVFI_STAGES-1];
  assign rvfi_intr      = rvfi_stage_intr     [RVFI_STAGES-1];
  assign rvfi_mode      = rvfi_stage_mode     [RVFI_STAGES-1];
  assign rvfi_ixl       = rvfi_stage_ixl      [RVFI_STAGES-1];
  assign rvfi_rs1_addr  = rvfi_stage_rs1_addr [RVFI_STAGES-1];
  assign rvfi_rs2_addr  = rvfi_stage_rs2_addr [RVFI_STAGES-1];
  assign rvfi_rs3_addr  = rvfi_stage_rs3_addr [RVFI_STAGES-1];
  assign rvfi_rs1_rdata = rvfi_stage_rs1_rdata[RVFI_STAGES-1];
  assign rvfi_rs2_rdata = rvfi_stage_rs2_rdata[RVFI_STAGES-1];
  assign rvfi_rs3_rdata = rvfi_stage_rs3_rdata[RVFI_STAGES-1];
  assign rvfi_rd_addr   = rvfi_stage_rd_addr  [RVFI_STAGES-1];
  assign rvfi_rd_wdata  = rvfi_stage_rd_wdata [RVFI_STAGES-1];
  assign rvfi_pc_rdata  = rvfi_stage_pc_rdata [RVFI_STAGES-1];
  assign rvfi_pc_wdata  = rvfi_stage_pc_wdata [RVFI_STAGES-1];
  assign rvfi_mem_addr  = rvfi_stage_mem_addr [RVFI_STAGES-1];
  assign rvfi_mem_rmask = rvfi_stage_mem_rmask[RVFI_STAGES-1];
  assign rvfi_mem_wmask = rvfi_stage_mem_wmask[RVFI_STAGES-1];
  assign rvfi_mem_rdata = rvfi_stage_mem_rdata[RVFI_STAGES-1];
  assign rvfi_mem_wdata = rvfi_stage_mem_wdata[RVFI_STAGES-1];

  assign rvfi_rd_addr_wb  = rf_waddr_wb;
  assign rvfi_rd_wdata_wb = rf_we_wb ? rf_wdata_wb : rf_wdata_lsu;
  assign rvfi_rd_we_wb    = rf_we_wb | rf_we_lsu;

  always_comb begin
    // Use always_comb instead of continuous assign so first assign can set 0 as default everywhere
    // that is overridden by more specific settings.
    rvfi_ext_mip                                     = '0;
    rvfi_ext_mip[CSR_MSIX_BIT]                       = rvfi_ext_stage_mip[RVFI_STAGES].irq_software;
    rvfi_ext_mip[CSR_MTIX_BIT]                       = rvfi_ext_stage_mip[RVFI_STAGES].irq_timer;
    rvfi_ext_mip[CSR_MEIX_BIT]                       = rvfi_ext_stage_mip[RVFI_STAGES].irq_external;
    rvfi_ext_mip[CSR_MFIX_BIT_HIGH:CSR_MFIX_BIT_LOW] = rvfi_ext_stage_mip[RVFI_STAGES].irq_fast;
  end

  assign rvfi_ext_nmi       = rvfi_ext_stage_nmi[RVFI_STAGES];
  assign rvfi_ext_debug_req = rvfi_ext_stage_debug_req[RVFI_STAGES];
  assign rvfi_ext_mcycle    = rvfi_ext_stage_mcycle[RVFI_STAGES-1];

  // When an instruction takes a trap the `rvfi_trap` signal will be set. Instructions that take
  // traps flush the pipeline so ordinarily wouldn't be seen to be retire. The RVFI tracking
  // pipeline is kept going for flushed instructions that trapped so they are still visible on the
  // RVFI interface.

  // Factor in exceptions taken in ID so RVFI tracking picks up flushed instructions that took
  // a trap
  assign rvfi_id_done = instr_id_done | (id_stage_i.controller_i.rvfi_flush_next &
                                         id_stage_i.controller_i.id_exception_o);

  if (WritebackStage) begin : gen_rvfi_wb_stage
    logic unused_instr_new_id;

    assign unused_instr_new_id = instr_new_id;

    // With writeback stage first RVFI stage buffers instruction information captured in ID/EX
    // awaiting instruction retirement and RF Write data/Mem read data whilst instruction is in WB
    // So first stage becomes valid when instruction leaves ID/EX stage and remains valid until
    // instruction leaves WB
    assign rvfi_stage_valid_d[0] = (rvfi_id_done & ~dummy_instr_id) |
                                   (rvfi_stage_valid[0] & ~rvfi_wb_done);
    // Second stage is output stage so simple valid cycle after instruction leaves WB (and so has
    // retired)
    assign rvfi_stage_valid_d[1] = rvfi_wb_done;

    // Signal new instruction in WB cycle after instruction leaves ID/EX (to enter WB)
    logic rvfi_instr_new_wb_q;

    // Signal new instruction in WB either when one has just entered or when a trap is progressing
    // through the tracking pipeline
    assign rvfi_instr_new_wb = rvfi_instr_new_wb_q | (rvfi_stage_valid[0] & rvfi_stage_trap[0]);

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rvfi_instr_new_wb_q <= 0;
      end else begin
        rvfi_instr_new_wb_q <= rvfi_id_done;
      end
    end

    assign rvfi_trap_id = id_stage_i.controller_i.id_exception_o;
    assign rvfi_trap_wb = id_stage_i.controller_i.exc_req_lsu;
    // WB is instantly done in the tracking pipeline when a trap is progress through the pipeline
    assign rvfi_wb_done = instr_done_wb | (rvfi_stage_valid[0] & rvfi_stage_trap[0]);
  end else begin : gen_rvfi_no_wb_stage
    // Without writeback stage first RVFI stage is output stage so simply valid the cycle after
    // instruction leaves ID/EX (and so has retired)
    assign rvfi_stage_valid_d[0] = rvfi_id_done & ~dummy_instr_id;
    // Without writeback stage signal new instr_new_wb when instruction enters ID/EX to correctly
    // setup register write signals
    assign rvfi_instr_new_wb = instr_new_id;
    assign rvfi_trap_id = id_stage_i.controller_i.exc_req_d | id_stage_i.controller_i.exc_req_lsu;
    assign rvfi_trap_wb = 1'b0;
    assign rvfi_wb_done = instr_done_wb;
  end

  assign rvfi_stage_order_d = dummy_instr_id ? rvfi_stage_order[0] : rvfi_stage_order[0] + 64'd1;

  // For interrupts and debug Ibex will take the relevant trap as soon as whatever instruction in ID
  // finishes or immediately if the ID stage is empty. The rvfi_ext interface provides the DV
  // environment with information about the irq/debug_req/nmi state that applies to a particular
  // instruction.
  //
  // When a irq/debug_req/nmi appears the ID stage will finish whatever instruction it is currently
  // executing (if any) then take the trap the cycle after that instruction leaves the ID stage. The
  // trap taken depends upon the state of irq/debug_req/nmi on that cycle. In the cycles following
  // that before the first instruction of the trap handler enters the ID stage the state of
  // irq/debug_req/nmi could change but this has no effect on the trap handler (e.g. a higher
  // priority interrupt might appear but this wouldn't stop the lower priority interrupt trap
  // handler executing first as it's already being fetched). To provide the DV environment with the
  // correct information for it to verify execution we need to capture the irq/debug_req/nmi state
  // the cycle the trap decision is made. Which the captured_X signals below do.
  //
  // The new_X signals take the raw irq/debug_req/nmi inputs and factor in the enable terms required
  // to determine if a trap will actually happen.
  //
  // These signals and the comment above are referred to in the documentation (cosim.rst). If
  // altering the names or meanings of these signals or this comment please adjust the documentation
  // appropriately.
  assign new_debug_req = (debug_req_i & ~debug_mode);
  assign new_nmi = irq_nm_i & ~nmi_mode & ~debug_mode;
  assign new_irq = irq_pending_o & csr_mstatus_mie & ~nmi_mode & ~debug_mode;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      captured_valid     <= 1'b0;
      captured_mip       <= '0;
      captured_nmi       <= 1'b0;
      captured_debug_req <= 1'b0;
    end else  begin
      // Capture when ID stage has emptied out and something occurs that will cause a trap and we
      // haven't yet captured
      if (~instr_valid_id & (new_debug_req | new_irq | new_nmi) & ~captured_valid) begin
        captured_valid     <= 1'b1;
        captured_nmi       <= irq_nm_i;
        captured_mip       <= cs_registers_i.mip;
        captured_debug_req <= debug_req_i;
      end

      // Capture cleared out as soon as a new instruction appears in ID
      if (if_stage_i.instr_valid_id_d) begin
        captured_valid <= 1'b0;
      end
    end
  end

  // Pass the captured irq/debug_req/nmi state to the rvfi_ext interface tracking pipeline.
  //
  // To correctly capture we need to factor in various enable terms, should there be a fault in this
  // logic we won't tell the DV environment about a trap that should have been taken. So if there's
  // no valid capture we grab the raw values of the irq/debug_req/nmi inputs whatever they are and
  // the DV environment will see if a trap should have been taken but wasn't.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_ext_stage_mip[0]       <= '0;
      rvfi_ext_stage_nmi[0]       <= '0;
      rvfi_ext_stage_debug_req[0] <= '0;
    end else if (if_stage_i.instr_valid_id_d & if_stage_i.instr_new_id_d) begin
      rvfi_ext_stage_mip[0]       <= instr_valid_id | ~captured_valid ? cs_registers_i.mip :
                                                                        captured_mip;
      rvfi_ext_stage_nmi[0]       <= instr_valid_id | ~captured_valid ? irq_nm_i :
                                                                        captured_nmi;
      rvfi_ext_stage_debug_req[0] <= instr_valid_id | ~captured_valid ? debug_req_i        :
                                                                        captured_debug_req;
    end
  end

  for (genvar i = 0; i < RVFI_STAGES; i = i + 1) begin : g_rvfi_stages
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rvfi_stage_halt[i]            <= '0;
        rvfi_stage_trap[i]            <= '0;
        rvfi_stage_intr[i]            <= '0;
        rvfi_stage_order[i]           <= '0;
        rvfi_stage_insn[i]            <= '0;
        rvfi_stage_mode[i]            <= {PRIV_LVL_M};
        rvfi_stage_ixl[i]             <= CSR_MISA_MXL;
        rvfi_stage_rs1_addr[i]        <= '0;
        rvfi_stage_rs2_addr[i]        <= '0;
        rvfi_stage_rs3_addr[i]        <= '0;
        rvfi_stage_pc_rdata[i]        <= '0;
        rvfi_stage_pc_wdata[i]        <= '0;
        rvfi_stage_mem_rmask[i]       <= '0;
        rvfi_stage_mem_wmask[i]       <= '0;
        rvfi_stage_valid[i]           <= '0;
        rvfi_stage_rs1_rdata[i]       <= '0;
        rvfi_stage_rs2_rdata[i]       <= '0;
        rvfi_stage_rs3_rdata[i]       <= '0;
        rvfi_stage_rd_wdata[i]        <= '0;
        rvfi_stage_rd_addr[i]         <= '0;
        rvfi_stage_mem_rdata[i]       <= '0;
        rvfi_stage_mem_wdata[i]       <= '0;
        rvfi_stage_mem_addr[i]        <= '0;
        rvfi_ext_stage_mip[i+1]       <= '0;
        rvfi_ext_stage_nmi[i+1]       <= '0;
        rvfi_ext_stage_debug_req[i+1] <= '0;
        rvfi_ext_stage_mcycle[i]      <= '0;
      end else begin
        rvfi_stage_valid[i] <= rvfi_stage_valid_d[i];

        if (i == 0) begin
          if (rvfi_id_done) begin
            rvfi_stage_halt[i]      <= '0;
            // TODO: Sort this out for writeback stage
            rvfi_stage_trap[i]            <= rvfi_trap_id;
            rvfi_stage_intr[i]            <= rvfi_intr_d;
            rvfi_stage_order[i]           <= rvfi_stage_order_d;
            rvfi_stage_insn[i]            <= rvfi_insn_id;
            rvfi_stage_mode[i]            <= {priv_mode_id};
            rvfi_stage_ixl[i]             <= CSR_MISA_MXL;
            rvfi_stage_rs1_addr[i]        <= rvfi_rs1_addr_d;
            rvfi_stage_rs2_addr[i]        <= rvfi_rs2_addr_d;
            rvfi_stage_rs3_addr[i]        <= rvfi_rs3_addr_d;
            rvfi_stage_pc_rdata[i]        <= pc_id;
            rvfi_stage_pc_wdata[i]        <= pc_set ? branch_target_ex : pc_if;
            rvfi_stage_mem_rmask[i]       <= rvfi_mem_mask_int;
            rvfi_stage_mem_wmask[i]       <= data_we_o ? rvfi_mem_mask_int : 4'b0000;
            rvfi_stage_rs1_rdata[i]       <= rvfi_rs1_data_d;
            rvfi_stage_rs2_rdata[i]       <= rvfi_rs2_data_d;
            rvfi_stage_rs3_rdata[i]       <= rvfi_rs3_data_d;
            rvfi_stage_rd_addr[i]         <= rvfi_rd_addr_d;
            rvfi_stage_rd_wdata[i]        <= rvfi_rd_wdata_d;
            rvfi_stage_mem_rdata[i]       <= rvfi_mem_rdata_d;
            rvfi_stage_mem_wdata[i]       <= rvfi_mem_wdata_d;
            rvfi_stage_mem_addr[i]        <= rvfi_mem_addr_d;
            rvfi_ext_stage_mip[i+1]       <= rvfi_ext_stage_mip[i];
            rvfi_ext_stage_nmi[i+1]       <= rvfi_ext_stage_nmi[i];
            rvfi_ext_stage_debug_req[i+1] <= rvfi_ext_stage_debug_req[i];
            rvfi_ext_stage_mcycle[i]      <= cs_registers_i.mcycle_counter_i.counter_val_o;
          end
        end else begin
          if (rvfi_wb_done) begin
            rvfi_stage_halt[i]      <= rvfi_stage_halt[i-1];
            rvfi_stage_trap[i]      <= rvfi_stage_trap[i-1] | rvfi_trap_wb;
            rvfi_stage_intr[i]      <= rvfi_stage_intr[i-1];
            rvfi_stage_order[i]     <= rvfi_stage_order[i-1];
            rvfi_stage_insn[i]      <= rvfi_stage_insn[i-1];
            rvfi_stage_mode[i]      <= rvfi_stage_mode[i-1];
            rvfi_stage_ixl[i]       <= rvfi_stage_ixl[i-1];
            rvfi_stage_rs1_addr[i]  <= rvfi_stage_rs1_addr[i-1];
            rvfi_stage_rs2_addr[i]  <= rvfi_stage_rs2_addr[i-1];
            rvfi_stage_rs3_addr[i]  <= rvfi_stage_rs3_addr[i-1];
            rvfi_stage_pc_rdata[i]  <= rvfi_stage_pc_rdata[i-1];
            rvfi_stage_pc_wdata[i]  <= rvfi_stage_pc_wdata[i-1];
            rvfi_stage_mem_rmask[i] <= rvfi_stage_mem_rmask[i-1];
            rvfi_stage_mem_wmask[i] <= rvfi_stage_mem_wmask[i-1];
            rvfi_stage_rs1_rdata[i] <= rvfi_stage_rs1_rdata[i-1];
            rvfi_stage_rs2_rdata[i] <= rvfi_stage_rs2_rdata[i-1];
            rvfi_stage_rs3_rdata[i] <= rvfi_stage_rs3_rdata[i-1];
            rvfi_stage_mem_wdata[i] <= rvfi_stage_mem_wdata[i-1];
            rvfi_stage_mem_addr[i]  <= rvfi_stage_mem_addr[i-1];

            // For 2 RVFI_STAGES/Writeback Stage ignore first stage flops for rd_addr, rd_wdata and
            // mem_rdata. For RF write addr/data actual write happens in writeback so capture
            // address/data there. For mem_rdata that is only available from the writeback stage.
            // Previous stage flops still exist in RTL as they are used by the non writeback config
            rvfi_stage_rd_addr[i]   <= rvfi_rd_addr_d;
            rvfi_stage_rd_wdata[i]  <= rvfi_rd_wdata_d;
            rvfi_stage_mem_rdata[i] <= rvfi_mem_rdata_d;

            rvfi_ext_stage_mip[i+1]       <= rvfi_ext_stage_mip[i];
            rvfi_ext_stage_nmi[i+1]       <= rvfi_ext_stage_nmi[i];
            rvfi_ext_stage_debug_req[i+1] <= rvfi_ext_stage_debug_req[i];
            rvfi_ext_stage_mcycle[i]      <= rvfi_ext_stage_mcycle[i-1];
          end
        end
      end
    end
  end


  // Memory adddress/write data available first cycle of ld/st instruction from register read
  always_comb begin
    if (instr_first_cycle_id) begin
      rvfi_mem_addr_d  = alu_adder_result_ex;
      rvfi_mem_wdata_d = lsu_wdata;
    end else begin
      rvfi_mem_addr_d  = rvfi_mem_addr_q;
      rvfi_mem_wdata_d = rvfi_mem_wdata_q;
    end
  end

  // Capture read data from LSU when it becomes valid
  always_comb begin
    if (lsu_resp_valid) begin
      rvfi_mem_rdata_d = rf_wdata_lsu;
    end else begin
      rvfi_mem_rdata_d = rvfi_mem_rdata_q;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_mem_addr_q  <= '0;
      rvfi_mem_rdata_q <= '0;
      rvfi_mem_wdata_q <= '0;
    end else begin
      rvfi_mem_addr_q  <= rvfi_mem_addr_d;
      rvfi_mem_rdata_q <= rvfi_mem_rdata_d;
      rvfi_mem_wdata_q <= rvfi_mem_wdata_d;
    end
  end
  // Byte enable based on data type
  always_comb begin
    unique case (lsu_type)
      2'b00:   rvfi_mem_mask_int = 4'b1111;
      2'b01:   rvfi_mem_mask_int = 4'b0011;
      2'b10:   rvfi_mem_mask_int = 4'b0001;
      default: rvfi_mem_mask_int = 4'b0000;
    endcase
  end

  always_comb begin
    if (instr_is_compressed_id) begin
      rvfi_insn_id = {16'b0, instr_rdata_c_id};
    end else begin
      rvfi_insn_id = instr_rdata_id;
    end
  end

  // Source registers 1 and 2 are read in the first instruction cycle
  // Source register 3 is read in the second instruction cycle.
  always_comb begin
    if (instr_first_cycle_id) begin
      rvfi_rs1_data_d = rf_ren_a ? multdiv_operand_a_ex : '0;
      rvfi_rs1_addr_d = rf_ren_a ? rf_raddr_a : '0;
      rvfi_rs2_data_d = rf_ren_b ? multdiv_operand_b_ex : '0;
      rvfi_rs2_addr_d = rf_ren_b ? rf_raddr_b : '0;
      rvfi_rs3_data_d = '0;
      rvfi_rs3_addr_d = '0;
    end else begin
      rvfi_rs1_data_d = rvfi_rs1_data_q;
      rvfi_rs1_addr_d = rvfi_rs1_addr_q;
      rvfi_rs2_data_d = rvfi_rs2_data_q;
      rvfi_rs2_addr_d = rvfi_rs2_addr_q;
      rvfi_rs3_data_d = multdiv_operand_a_ex;
      rvfi_rs3_addr_d = rf_raddr_a;
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_rs1_data_q <= '0;
      rvfi_rs1_addr_q <= '0;
      rvfi_rs2_data_q <= '0;
      rvfi_rs2_addr_q <= '0;

    end else begin
      rvfi_rs1_data_q <= rvfi_rs1_data_d;
      rvfi_rs1_addr_q <= rvfi_rs1_addr_d;
      rvfi_rs2_data_q <= rvfi_rs2_data_d;
      rvfi_rs2_addr_q <= rvfi_rs2_addr_d;
    end
  end

  always_comb begin
    if (rvfi_rd_we_wb) begin
      // Capture address/data of write to register file
      rvfi_rd_addr_d = rvfi_rd_addr_wb;
      // If writing to x0 zero write data as required by RVFI specification
      if (rvfi_rd_addr_wb == 5'b0) begin
        rvfi_rd_wdata_d = '0;
      end else begin
        rvfi_rd_wdata_d = rvfi_rd_wdata_wb;
      end
    end else if (rvfi_instr_new_wb) begin
      // If no RF write but new instruction in Writeback (when present) or ID/EX (when no writeback
      // stage present) then zero RF write address/data as required by RVFI specification
      rvfi_rd_addr_d  = '0;
      rvfi_rd_wdata_d = '0;
    end else begin
      // Otherwise maintain previous value
      rvfi_rd_addr_d  = rvfi_rd_addr_q;
      rvfi_rd_wdata_d = rvfi_rd_wdata_q;
    end
  end

  // RD write register is refreshed only once per cycle and
  // then it is kept stable for the cycle.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_rd_addr_q    <= '0;
      rvfi_rd_wdata_q   <= '0;
    end else begin
      rvfi_rd_addr_q    <= rvfi_rd_addr_d;
      rvfi_rd_wdata_q   <= rvfi_rd_wdata_d;
    end
  end

  // rvfi_intr must be set for first instruction that is part of a trap handler.
  // On the first cycle of a new instruction see if a trap PC was set by the previous instruction,
  // otherwise maintain value.
  assign rvfi_intr_d = instr_first_cycle_id ? rvfi_set_trap_pc_q : rvfi_intr_q;

  always_comb begin
    rvfi_set_trap_pc_d = rvfi_set_trap_pc_q;

    if (pc_set && pc_mux_id == PC_EXC &&
        (exc_pc_mux_id == EXC_PC_EXC || exc_pc_mux_id == EXC_PC_IRQ)) begin
      // PC is set to enter a trap handler
      rvfi_set_trap_pc_d = 1'b1;
    end else if (rvfi_set_trap_pc_q && rvfi_id_done) begin
      // first instruction has been executed after PC is set to trap handler
      rvfi_set_trap_pc_d = 1'b0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_set_trap_pc_q <= 1'b0;
      rvfi_intr_q        <= 1'b0;
    end else begin
      rvfi_set_trap_pc_q <= rvfi_set_trap_pc_d;
      rvfi_intr_q        <= rvfi_intr_d;
    end
  end

`else
  logic unused_instr_new_id, unused_instr_id_done, unused_instr_done_wb;
  assign unused_instr_id_done = instr_id_done;
  assign unused_instr_new_id = instr_new_id;
  assign unused_instr_done_wb = instr_done_wb;
`endif

  // Certain parameter combinations are not supported
  `ASSERT_INIT(IllegalParamSecure, !(SecureIbex && (RV32M == RV32MNone)))


  //////////
  // FCOV //
  //////////

`ifndef SYNTHESIS
  // fcov signals for CSR access. These are complicated by illegal accesses. Where an access is
  // legal `csr_op_en` signals the operation occurring, but this is deasserted where an access is
  // illegal. Instead `illegal_insn_id` confirms the instruction is taking an illegal instruction
  // exception.
  // All CSR operations perform a read, `CSR_OP_READ` is the only one that only performs a read
  `DV_FCOV_SIGNAL(logic, csr_read_only,
      (csr_op == CSR_OP_READ) && csr_access && (csr_op_en || illegal_insn_id))
  `DV_FCOV_SIGNAL(logic, csr_write,
      cs_registers_i.csr_wr && csr_access && (csr_op_en || illegal_insn_id))

  if (PMPEnable) begin : g_pmp_fcov_signals
    logic [PMPNumRegions-1:0] fcov_pmp_region_ichan_priority;
    logic [PMPNumRegions-1:0] fcov_pmp_region_ichan2_priority;
    logic [PMPNumRegions-1:0] fcov_pmp_region_dchan_priority;

    logic unused_fcov_pmp_region_priority;

    assign unused_fcov_pmp_region_priority = ^{fcov_pmp_region_ichan_priority,
                                               fcov_pmp_region_ichan2_priority,
                                               fcov_pmp_region_dchan_priority};

    for (genvar i_region = 0; i_region < PMPNumRegions; i_region += 1) begin : g_pmp_region_fcov
      `DV_FCOV_SIGNAL(logic, pmp_region_ichan_access,
          g_pmp.pmp_i.region_match_all[PMP_I][i_region] & if_stage_i.if_id_pipe_reg_we)
      `DV_FCOV_SIGNAL(logic, pmp_region_ichan2_access,
          g_pmp.pmp_i.region_match_all[PMP_I2][i_region] & if_stage_i.if_id_pipe_reg_we)
      `DV_FCOV_SIGNAL(logic, pmp_region_dchan_access,
          g_pmp.pmp_i.region_match_all[PMP_D][i_region] & data_req_out)

      if (i_region > 0) begin : g_region_priority
        assign fcov_pmp_region_ichan_priority[i_region] =
          g_pmp.pmp_i.region_match_all[PMP_I][i_region] &
          ~|g_pmp.pmp_i.region_match_all[PMP_I][i_region-1:0];

        assign fcov_pmp_region_ichan2_priority[i_region] =
          g_pmp.pmp_i.region_match_all[PMP_I2][i_region] &
          ~|g_pmp.pmp_i.region_match_all[PMP_I2][i_region-1:0];

        assign fcov_pmp_region_dchan_priority[i_region] =
          g_pmp.pmp_i.region_match_all[PMP_D][i_region] &
          ~|g_pmp.pmp_i.region_match_all[PMP_D][i_region-1:0];
      end else begin : g_region_highest_priority
        assign fcov_pmp_region_ichan_priority[i_region] =
          g_pmp.pmp_i.region_match_all[PMP_I][i_region];

        assign fcov_pmp_region_ichan2_priority[i_region] =
          g_pmp.pmp_i.region_match_all[PMP_I2][i_region];

        assign fcov_pmp_region_dchan_priority[i_region] =
          g_pmp.pmp_i.region_match_all[PMP_D][i_region];
      end
    end
  end
`endif

endmodule
