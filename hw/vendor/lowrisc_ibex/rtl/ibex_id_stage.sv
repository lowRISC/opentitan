// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

/**
 * Instruction Decode Stage
 *
 * Decode stage of the core. It decodes the instructions and hosts the register
 * file.
 */

`include "prim_assert.sv"
`include "dv_fcov_macros.svh"

module ibex_id_stage #(
  parameter bit               RV32E           = 0,
  parameter ibex_pkg::rv32m_e RV32M           = ibex_pkg::RV32MFast,
  parameter ibex_pkg::rv32b_e RV32B           = ibex_pkg::RV32BNone,
  parameter bit               DataIndTiming   = 1'b0,
  parameter bit               BranchTargetALU = 0,
  parameter bit               WritebackStage  = 0,
  parameter bit               BranchPredictor = 0,
  parameter bit               MemECC          = 1'b0
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  output logic                      ctrl_busy_o,
  output logic                      illegal_insn_o,

  // Interface to IF stage
  input  logic                      instr_valid_i,
  input  logic [31:0]               instr_rdata_i,         // from IF-ID pipeline registers
  input  logic [31:0]               instr_rdata_alu_i,     // from IF-ID pipeline registers
  input  logic [15:0]               instr_rdata_c_i,       // from IF-ID pipeline registers
  input  logic                      instr_is_compressed_i,
  input  logic                      instr_bp_taken_i,
  output logic                      instr_req_o,
  output logic                      instr_first_cycle_id_o,
  output logic                      instr_valid_clear_o,   // kill instr in IF-ID reg
  output logic                      id_in_ready_o,         // ID stage is ready for next instr
  input  logic                      instr_exec_i,
  output logic                      icache_inval_o,

  // Jumps and branches
  input  logic                      branch_decision_i,

  // IF and ID stage signals
  output logic                      pc_set_o,
  output ibex_pkg::pc_sel_e         pc_mux_o,
  output logic                      nt_branch_mispredict_o,
  output logic [31:0]               nt_branch_addr_o,
  output ibex_pkg::exc_pc_sel_e     exc_pc_mux_o,
  output ibex_pkg::exc_cause_t      exc_cause_o,

  input  logic                      illegal_c_insn_i,
  input  logic                      instr_fetch_err_i,
  input  logic                      instr_fetch_err_plus2_i,

  input  logic [31:0]               pc_id_i,

  // Stalls
  input  logic                      ex_valid_i,       // EX stage has valid output
  input  logic                      lsu_resp_valid_i, // LSU has valid output, or is done
  // ALU
  output ibex_pkg::alu_op_e         alu_operator_ex_o,
  output logic [31:0]               alu_operand_a_ex_o,
  output logic [31:0]               alu_operand_b_ex_o,

  // Multicycle Operation Stage Register
  input  logic [1:0]                imd_val_we_ex_i,
  input  logic [33:0]               imd_val_d_ex_i[2],
  output logic [33:0]               imd_val_q_ex_o[2],

  // Branch target ALU
  output logic [31:0]               bt_a_operand_o,
  output logic [31:0]               bt_b_operand_o,

  // MUL, DIV
  output logic                      mult_en_ex_o,
  output logic                      div_en_ex_o,
  output logic                      mult_sel_ex_o,
  output logic                      div_sel_ex_o,
  output ibex_pkg::md_op_e          multdiv_operator_ex_o,
  output logic  [1:0]               multdiv_signed_mode_ex_o,
  output logic [31:0]               multdiv_operand_a_ex_o,
  output logic [31:0]               multdiv_operand_b_ex_o,
  output logic                      multdiv_ready_id_o,

  // CSR
  output logic                      csr_access_o,
  output ibex_pkg::csr_op_e         csr_op_o,
  output logic                      csr_op_en_o,
  output logic                      csr_save_if_o,
  output logic                      csr_save_id_o,
  output logic                      csr_save_wb_o,
  output logic                      csr_restore_mret_id_o,
  output logic                      csr_restore_dret_id_o,
  output logic                      csr_save_cause_o,
  output logic [31:0]               csr_mtval_o,
  input  ibex_pkg::priv_lvl_e       priv_mode_i,
  input  logic                      csr_mstatus_tw_i,
  input  logic                      illegal_csr_insn_i,
  input  logic                      data_ind_timing_i,

  // Interface to load store unit
  output logic                      lsu_req_o,
  output logic                      lsu_we_o,
  output logic [1:0]                lsu_type_o,
  output logic                      lsu_sign_ext_o,
  output logic [31:0]               lsu_wdata_o,

  input  logic                      lsu_req_done_i, // Data req to LSU is complete and
                                                    // instruction can move to writeback
                                                    // (only relevant where writeback stage is
                                                    // present)

  input  logic                      lsu_addr_incr_req_i,
  input  logic [31:0]               lsu_addr_last_i,

  // Interrupt signals
  input  logic                      csr_mstatus_mie_i,
  input  logic                      irq_pending_i,
  input  ibex_pkg::irqs_t           irqs_i,
  input  logic                      irq_nm_i,
  output logic                      nmi_mode_o,

  input  logic                      lsu_load_err_i,
  input  logic                      lsu_load_resp_intg_err_i,
  input  logic                      lsu_store_err_i,
  input  logic                      lsu_store_resp_intg_err_i,

  // Debug Signal
  output logic                      debug_mode_o,
  output logic                      debug_mode_entering_o,
  output ibex_pkg::dbg_cause_e      debug_cause_o,
  output logic                      debug_csr_save_o,
  input  logic                      debug_req_i,
  input  logic                      debug_single_step_i,
  input  logic                      debug_ebreakm_i,
  input  logic                      debug_ebreaku_i,
  input  logic                      trigger_match_i,

  // Write back signal
  input  logic [31:0]               result_ex_i,
  input  logic [31:0]               csr_rdata_i,

  // Register file read
  output logic [4:0]                rf_raddr_a_o,
  input  logic [31:0]               rf_rdata_a_i,
  output logic [4:0]                rf_raddr_b_o,
  input  logic [31:0]               rf_rdata_b_i,
  output logic                      rf_ren_a_o,
  output logic                      rf_ren_b_o,

  // Register file write (via writeback)
  output logic [4:0]                rf_waddr_id_o,
  output logic [31:0]               rf_wdata_id_o,
  output logic                      rf_we_id_o,
  output logic                      rf_rd_a_wb_match_o,
  output logic                      rf_rd_b_wb_match_o,

  // Register write information from writeback (for resolving data hazards)
  input  logic [4:0]                rf_waddr_wb_i,
  input  logic [31:0]               rf_wdata_fwd_wb_i,
  input  logic                      rf_write_wb_i,

  output  logic                     en_wb_o,
  output  ibex_pkg::wb_instr_type_e instr_type_wb_o,
  output  logic                     instr_perf_count_id_o,
  input logic                       ready_wb_i,
  input logic                       outstanding_load_wb_i,
  input logic                       outstanding_store_wb_i,

  // Performance Counters
  output logic                      perf_jump_o,    // executing a jump instr
  output logic                      perf_branch_o,  // executing a branch instr
  output logic                      perf_tbranch_o, // executing a taken branch instr
  output logic                      perf_dside_wait_o, // instruction in ID/EX is awaiting memory
                                                        // access to finish before proceeding
  output logic                      perf_mul_wait_o,
  output logic                      perf_div_wait_o,
  output logic                      instr_id_done_o
);

  import ibex_pkg::*;

  // Decoder/Controller, ID stage internal signals
  logic        illegal_insn_dec;
  logic        illegal_dret_insn;
  logic        illegal_umode_insn;
  logic        ebrk_insn;
  logic        mret_insn_dec;
  logic        dret_insn_dec;
  logic        ecall_insn_dec;
  logic        wfi_insn_dec;

  logic        wb_exception;
  logic        id_exception;

  logic        branch_in_dec;
  logic        branch_set, branch_set_raw, branch_set_raw_d;
  logic        branch_jump_set_done_q, branch_jump_set_done_d;
  logic        branch_not_set;
  logic        branch_taken;
  logic        jump_in_dec;
  logic        jump_set_dec;
  logic        jump_set, jump_set_raw;

  logic        instr_first_cycle;
  logic        instr_executing_spec;
  logic        instr_executing;
  logic        instr_done;
  logic        controller_run;
  logic        stall_ld_hz;
  logic        stall_mem;
  logic        stall_multdiv;
  logic        stall_branch;
  logic        stall_jump;
  logic        stall_id;
  logic        stall_wb;
  logic        flush_id;
  logic        multicycle_done;

  logic        mem_resp_intg_err;

  // Immediate decoding and sign extension
  logic [31:0] imm_i_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_b_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_j_type;
  logic [31:0] zimm_rs1_type;

  logic [31:0] imm_a;       // contains the immediate for operand b
  logic [31:0] imm_b;       // contains the immediate for operand b

  // Register file interface

  rf_wd_sel_e  rf_wdata_sel;
  logic        rf_we_dec, rf_we_raw;
  logic        rf_ren_a, rf_ren_b;
  logic        rf_ren_a_dec, rf_ren_b_dec;

  // Read enables should only be asserted for valid and legal instructions
  assign rf_ren_a = instr_valid_i & ~instr_fetch_err_i & ~illegal_insn_o & rf_ren_a_dec;
  assign rf_ren_b = instr_valid_i & ~instr_fetch_err_i & ~illegal_insn_o & rf_ren_b_dec;

  assign rf_ren_a_o = rf_ren_a;
  assign rf_ren_b_o = rf_ren_b;

  logic [31:0] rf_rdata_a_fwd;
  logic [31:0] rf_rdata_b_fwd;

  // ALU Control
  alu_op_e     alu_operator;
  op_a_sel_e   alu_op_a_mux_sel, alu_op_a_mux_sel_dec;
  op_b_sel_e   alu_op_b_mux_sel, alu_op_b_mux_sel_dec;
  logic        alu_multicycle_dec;
  logic        stall_alu;

  logic [33:0] imd_val_q[2];

  op_a_sel_e   bt_a_mux_sel;
  imm_b_sel_e  bt_b_mux_sel;

  imm_a_sel_e  imm_a_mux_sel;
  imm_b_sel_e  imm_b_mux_sel, imm_b_mux_sel_dec;

  // Multiplier Control
  logic        mult_en_id, mult_en_dec; // use integer multiplier
  logic        div_en_id, div_en_dec;   // use integer division or reminder
  logic        multdiv_en_dec;
  md_op_e      multdiv_operator;
  logic [1:0]  multdiv_signed_mode;

  // Data Memory Control
  logic        lsu_we;
  logic [1:0]  lsu_type;
  logic        lsu_sign_ext;
  logic        lsu_req, lsu_req_dec;
  logic        data_req_allowed;

  // CSR control
  logic        csr_pipe_flush;

  logic [31:0] alu_operand_a;
  logic [31:0] alu_operand_b;

  /////////////
  // LSU Mux //
  /////////////

  // Misaligned loads/stores result in two aligned loads/stores, compute second address
  assign alu_op_a_mux_sel = lsu_addr_incr_req_i ? OP_A_FWD        : alu_op_a_mux_sel_dec;
  assign alu_op_b_mux_sel = lsu_addr_incr_req_i ? OP_B_IMM        : alu_op_b_mux_sel_dec;
  assign imm_b_mux_sel    = lsu_addr_incr_req_i ? IMM_B_INCR_ADDR : imm_b_mux_sel_dec;

  ///////////////////
  // Operand MUXES //
  ///////////////////

  // Main ALU immediate MUX for Operand A
  assign imm_a = (imm_a_mux_sel == IMM_A_Z) ? zimm_rs1_type : '0;

  // Main ALU MUX for Operand A
  always_comb begin : alu_operand_a_mux
    unique case (alu_op_a_mux_sel)
      OP_A_REG_A:  alu_operand_a = rf_rdata_a_fwd;
      OP_A_FWD:    alu_operand_a = lsu_addr_last_i;
      OP_A_CURRPC: alu_operand_a = pc_id_i;
      OP_A_IMM:    alu_operand_a = imm_a;
      default:     alu_operand_a = pc_id_i;
    endcase
  end

  if (BranchTargetALU) begin : g_btalu_muxes
    // Branch target ALU operand A mux
    always_comb begin : bt_operand_a_mux
      unique case (bt_a_mux_sel)
        OP_A_REG_A:  bt_a_operand_o = rf_rdata_a_fwd;
        OP_A_CURRPC: bt_a_operand_o = pc_id_i;
        default:     bt_a_operand_o = pc_id_i;
      endcase
    end

    // Branch target ALU operand B mux
    always_comb begin : bt_immediate_b_mux
      unique case (bt_b_mux_sel)
        IMM_B_I:         bt_b_operand_o = imm_i_type;
        IMM_B_B:         bt_b_operand_o = imm_b_type;
        IMM_B_J:         bt_b_operand_o = imm_j_type;
        IMM_B_INCR_PC:   bt_b_operand_o = instr_is_compressed_i ? 32'h2 : 32'h4;
        default:         bt_b_operand_o = instr_is_compressed_i ? 32'h2 : 32'h4;
      endcase
    end

    // Reduced main ALU immediate MUX for Operand B
    always_comb begin : immediate_b_mux
      unique case (imm_b_mux_sel)
        IMM_B_I:         imm_b = imm_i_type;
        IMM_B_S:         imm_b = imm_s_type;
        IMM_B_U:         imm_b = imm_u_type;
        IMM_B_INCR_PC:   imm_b = instr_is_compressed_i ? 32'h2 : 32'h4;
        IMM_B_INCR_ADDR: imm_b = 32'h4;
        default:         imm_b = 32'h4;
      endcase
    end
    `ASSERT(IbexImmBMuxSelValid, instr_valid_i |-> imm_b_mux_sel inside {
        IMM_B_I,
        IMM_B_S,
        IMM_B_U,
        IMM_B_INCR_PC,
        IMM_B_INCR_ADDR})
  end else begin : g_nobtalu
    op_a_sel_e  unused_a_mux_sel;
    imm_b_sel_e unused_b_mux_sel;

    assign unused_a_mux_sel = bt_a_mux_sel;
    assign unused_b_mux_sel = bt_b_mux_sel;
    assign bt_a_operand_o   = '0;
    assign bt_b_operand_o   = '0;

    // Full main ALU immediate MUX for Operand B
    always_comb begin : immediate_b_mux
      unique case (imm_b_mux_sel)
        IMM_B_I:         imm_b = imm_i_type;
        IMM_B_S:         imm_b = imm_s_type;
        IMM_B_B:         imm_b = imm_b_type;
        IMM_B_U:         imm_b = imm_u_type;
        IMM_B_J:         imm_b = imm_j_type;
        IMM_B_INCR_PC:   imm_b = instr_is_compressed_i ? 32'h2 : 32'h4;
        IMM_B_INCR_ADDR: imm_b = 32'h4;
        default:         imm_b = 32'h4;
      endcase
    end
    `ASSERT(IbexImmBMuxSelValid, instr_valid_i |-> imm_b_mux_sel inside {
        IMM_B_I,
        IMM_B_S,
        IMM_B_B,
        IMM_B_U,
        IMM_B_J,
        IMM_B_INCR_PC,
        IMM_B_INCR_ADDR})
  end

  // ALU MUX for Operand B
  assign alu_operand_b = (alu_op_b_mux_sel == OP_B_IMM) ? imm_b : rf_rdata_b_fwd;

  /////////////////////////////////////////
  // Multicycle Operation Stage Register //
  /////////////////////////////////////////

  for (genvar i = 0; i < 2; i++) begin : gen_intermediate_val_reg
    always_ff @(posedge clk_i or negedge rst_ni) begin : intermediate_val_reg
      if (!rst_ni) begin
        imd_val_q[i] <= '0;
      end else if (imd_val_we_ex_i[i]) begin
        imd_val_q[i] <= imd_val_d_ex_i[i];
      end
    end
  end

  assign imd_val_q_ex_o = imd_val_q;

  ///////////////////////
  // Register File MUX //
  ///////////////////////

  // Suppress register write if there is an illegal CSR access or instruction is not executing
  assign rf_we_id_o = rf_we_raw & instr_executing & ~illegal_csr_insn_i;

  // Register file write data mux
  always_comb begin : rf_wdata_id_mux
    unique case (rf_wdata_sel)
      RF_WD_EX:  rf_wdata_id_o = result_ex_i;
      RF_WD_CSR: rf_wdata_id_o = csr_rdata_i;
      default:   rf_wdata_id_o = result_ex_i;
    endcase
  end

  /////////////
  // Decoder //
  /////////////

  ibex_decoder #(
    .RV32E          (RV32E),
    .RV32M          (RV32M),
    .RV32B          (RV32B),
    .BranchTargetALU(BranchTargetALU)
  ) decoder_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // controller
    .illegal_insn_o(illegal_insn_dec),
    .ebrk_insn_o   (ebrk_insn),
    .mret_insn_o   (mret_insn_dec),
    .dret_insn_o   (dret_insn_dec),
    .ecall_insn_o  (ecall_insn_dec),
    .wfi_insn_o    (wfi_insn_dec),
    .jump_set_o    (jump_set_dec),
    .branch_taken_i(branch_taken),
    .icache_inval_o(icache_inval_o),

    // from IF-ID pipeline register
    .instr_first_cycle_i(instr_first_cycle),
    .instr_rdata_i      (instr_rdata_i),
    .instr_rdata_alu_i  (instr_rdata_alu_i),
    .illegal_c_insn_i   (illegal_c_insn_i),

    // immediates
    .imm_a_mux_sel_o(imm_a_mux_sel),
    .imm_b_mux_sel_o(imm_b_mux_sel_dec),
    .bt_a_mux_sel_o (bt_a_mux_sel),
    .bt_b_mux_sel_o (bt_b_mux_sel),

    .imm_i_type_o   (imm_i_type),
    .imm_s_type_o   (imm_s_type),
    .imm_b_type_o   (imm_b_type),
    .imm_u_type_o   (imm_u_type),
    .imm_j_type_o   (imm_j_type),
    .zimm_rs1_type_o(zimm_rs1_type),

    // register file
    .rf_wdata_sel_o(rf_wdata_sel),
    .rf_we_o       (rf_we_dec),

    .rf_raddr_a_o(rf_raddr_a_o),
    .rf_raddr_b_o(rf_raddr_b_o),
    .rf_waddr_o  (rf_waddr_id_o),
    .rf_ren_a_o  (rf_ren_a_dec),
    .rf_ren_b_o  (rf_ren_b_dec),

    // ALU
    .alu_operator_o    (alu_operator),
    .alu_op_a_mux_sel_o(alu_op_a_mux_sel_dec),
    .alu_op_b_mux_sel_o(alu_op_b_mux_sel_dec),
    .alu_multicycle_o  (alu_multicycle_dec),

    // MULT & DIV
    .mult_en_o            (mult_en_dec),
    .div_en_o             (div_en_dec),
    .mult_sel_o           (mult_sel_ex_o),
    .div_sel_o            (div_sel_ex_o),
    .multdiv_operator_o   (multdiv_operator),
    .multdiv_signed_mode_o(multdiv_signed_mode),

    // CSRs
    .csr_access_o(csr_access_o),
    .csr_op_o    (csr_op_o),

    // LSU
    .data_req_o           (lsu_req_dec),
    .data_we_o            (lsu_we),
    .data_type_o          (lsu_type),
    .data_sign_extension_o(lsu_sign_ext),

    // jump/branches
    .jump_in_dec_o  (jump_in_dec),
    .branch_in_dec_o(branch_in_dec)
  );

  /////////////////////////////////
  // CSR-related pipeline flushes //
  /////////////////////////////////
  always_comb begin : csr_pipeline_flushes
    csr_pipe_flush = 1'b0;

    // A pipeline flush is needed to let the controller react after modifying certain CSRs:
    // - When enabling interrupts, pending IRQs become visible to the controller only during
    //   the next cycle. If during that cycle the core disables interrupts again, it does not
    //   see any pending IRQs and consequently does not start to handle interrupts.
    // - When modifying any PMP CSR, PMP check of the next instruction might get invalidated.
    //   Hence, a pipeline flush is needed to instantiate another PMP check with the updated CSRs.
    // - When modifying debug CSRs - TODO: Check if this is really needed
    if (csr_op_en_o == 1'b1 && (csr_op_o == CSR_OP_WRITE || csr_op_o == CSR_OP_SET)) begin
      if (csr_num_e'(instr_rdata_i[31:20]) == CSR_MSTATUS ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_MIE     ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_MSECCFG ||
          // To catch all PMPCFG/PMPADDR registers, get the shared top most 7 bits.
          instr_rdata_i[31:25] == 7'h1D) begin
        csr_pipe_flush = 1'b1;
      end
    end else if (csr_op_en_o == 1'b1 && csr_op_o != CSR_OP_READ) begin
      if (csr_num_e'(instr_rdata_i[31:20]) == CSR_DCSR      ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_DPC       ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_DSCRATCH0 ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_DSCRATCH1) begin
        csr_pipe_flush = 1'b1;
      end
    end
  end

  ////////////////
  // Controller //
  ////////////////

  // Executing DRET outside of Debug Mode causes an illegal instruction exception.
  assign illegal_dret_insn  = dret_insn_dec & ~debug_mode_o;
  // Some instructions can only be executed in M-Mode
  assign illegal_umode_insn = (priv_mode_i != PRIV_LVL_M) &
                              // MRET must be in M-Mode. TW means trap WFI to M-Mode.
                              (mret_insn_dec | (csr_mstatus_tw_i & wfi_insn_dec));

  assign illegal_insn_o = instr_valid_i &
      (illegal_insn_dec | illegal_csr_insn_i | illegal_dret_insn | illegal_umode_insn);

  assign mem_resp_intg_err = lsu_load_resp_intg_err_i | lsu_store_resp_intg_err_i;

  ibex_controller #(
    .WritebackStage (WritebackStage),
    .BranchPredictor(BranchPredictor),
    .MemECC(MemECC)
  ) controller_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .ctrl_busy_o(ctrl_busy_o),

    // decoder related signals
    .illegal_insn_i  (illegal_insn_o),
    .ecall_insn_i    (ecall_insn_dec),
    .mret_insn_i     (mret_insn_dec),
    .dret_insn_i     (dret_insn_dec),
    .wfi_insn_i      (wfi_insn_dec),
    .ebrk_insn_i     (ebrk_insn),
    .csr_pipe_flush_i(csr_pipe_flush),

    // from IF-ID pipeline
    .instr_valid_i          (instr_valid_i),
    .instr_i                (instr_rdata_i),
    .instr_compressed_i     (instr_rdata_c_i),
    .instr_is_compressed_i  (instr_is_compressed_i),
    .instr_bp_taken_i       (instr_bp_taken_i),
    .instr_fetch_err_i      (instr_fetch_err_i),
    .instr_fetch_err_plus2_i(instr_fetch_err_plus2_i),
    .pc_id_i                (pc_id_i),

    // to IF-ID pipeline
    .instr_valid_clear_o(instr_valid_clear_o),
    .id_in_ready_o      (id_in_ready_o),
    .controller_run_o   (controller_run),
    .instr_exec_i       (instr_exec_i),

    // to prefetcher
    .instr_req_o           (instr_req_o),
    .pc_set_o              (pc_set_o),
    .pc_mux_o              (pc_mux_o),
    .nt_branch_mispredict_o(nt_branch_mispredict_o),
    .exc_pc_mux_o          (exc_pc_mux_o),
    .exc_cause_o           (exc_cause_o),

    // LSU
    .lsu_addr_last_i    (lsu_addr_last_i),
    .load_err_i         (lsu_load_err_i),
    .mem_resp_intg_err_i(mem_resp_intg_err),
    .store_err_i        (lsu_store_err_i),
    .wb_exception_o     (wb_exception),
    .id_exception_o     (id_exception),

    // jump/branch control
    .branch_set_i     (branch_set),
    .branch_not_set_i (branch_not_set),
    .jump_set_i       (jump_set),

    // interrupt signals
    .csr_mstatus_mie_i(csr_mstatus_mie_i),
    .irq_pending_i    (irq_pending_i),
    .irqs_i           (irqs_i),
    .irq_nm_ext_i     (irq_nm_i),
    .nmi_mode_o       (nmi_mode_o),

    // CSR Controller Signals
    .csr_save_if_o        (csr_save_if_o),
    .csr_save_id_o        (csr_save_id_o),
    .csr_save_wb_o        (csr_save_wb_o),
    .csr_restore_mret_id_o(csr_restore_mret_id_o),
    .csr_restore_dret_id_o(csr_restore_dret_id_o),
    .csr_save_cause_o     (csr_save_cause_o),
    .csr_mtval_o          (csr_mtval_o),
    .priv_mode_i          (priv_mode_i),

    // Debug Signal
    .debug_mode_o         (debug_mode_o),
    .debug_mode_entering_o(debug_mode_entering_o),
    .debug_cause_o        (debug_cause_o),
    .debug_csr_save_o     (debug_csr_save_o),
    .debug_req_i          (debug_req_i),
    .debug_single_step_i  (debug_single_step_i),
    .debug_ebreakm_i      (debug_ebreakm_i),
    .debug_ebreaku_i      (debug_ebreaku_i),
    .trigger_match_i      (trigger_match_i),

    .stall_id_i(stall_id),
    .stall_wb_i(stall_wb),
    .flush_id_o(flush_id),
    .ready_wb_i(ready_wb_i),

    // Performance Counters
    .perf_jump_o   (perf_jump_o),
    .perf_tbranch_o(perf_tbranch_o)
  );

  assign multdiv_en_dec   = mult_en_dec | div_en_dec;

  assign lsu_req         = instr_executing ? data_req_allowed & lsu_req_dec  : 1'b0;
  assign mult_en_id      = instr_executing ? mult_en_dec                     : 1'b0;
  assign div_en_id       = instr_executing ? div_en_dec                      : 1'b0;

  assign lsu_req_o               = lsu_req;
  assign lsu_we_o                = lsu_we;
  assign lsu_type_o              = lsu_type;
  assign lsu_sign_ext_o          = lsu_sign_ext;
  assign lsu_wdata_o             = rf_rdata_b_fwd;
  // csr_op_en_o is set when CSR access should actually happen.
  // csv_access_o is set when CSR access instruction is present and is used to compute whether a CSR
  // access is illegal. A combinational loop would be created if csr_op_en_o was used along (as
  // asserting it for an illegal csr access would result in a flush that would need to deassert it).
  assign csr_op_en_o             = csr_access_o & instr_executing & instr_id_done_o;

  assign alu_operator_ex_o           = alu_operator;
  assign alu_operand_a_ex_o          = alu_operand_a;
  assign alu_operand_b_ex_o          = alu_operand_b;

  assign mult_en_ex_o                = mult_en_id;
  assign div_en_ex_o                 = div_en_id;

  assign multdiv_operator_ex_o       = multdiv_operator;
  assign multdiv_signed_mode_ex_o    = multdiv_signed_mode;
  assign multdiv_operand_a_ex_o      = rf_rdata_a_fwd;
  assign multdiv_operand_b_ex_o      = rf_rdata_b_fwd;

  ////////////////////////
  // Branch set control //
  ////////////////////////

  if (BranchTargetALU && !DataIndTiming) begin : g_branch_set_direct
    // Branch set fed straight to controller with branch target ALU
    // (condition pass/fail used same cycle as generated instruction request)
    assign branch_set_raw      = branch_set_raw_d;
  end else begin : g_branch_set_flop
    // SEC_CM: CORE.DATA_REG_SW.SCA
    // Branch set flopped without branch target ALU, or in fixed time execution mode
    // (condition pass/fail used next cycle where branch target is calculated)
    logic branch_set_raw_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        branch_set_raw_q <= 1'b0;
      end else begin
        branch_set_raw_q <= branch_set_raw_d;
      end
    end

    // Branches always take two cycles in fixed time execution mode, with or without the branch
    // target ALU (to avoid a path from the branch decision into the branch target ALU operand
    // muxing).
    assign branch_set_raw      = (BranchTargetALU && !data_ind_timing_i) ? branch_set_raw_d :
                                                                           branch_set_raw_q;

  end

  // Track whether the current instruction in ID/EX has done a branch or jump set.
  assign branch_jump_set_done_d = (branch_set_raw | jump_set_raw | branch_jump_set_done_q) &
    ~instr_valid_clear_o;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      branch_jump_set_done_q <= 1'b0;
    end else begin
      branch_jump_set_done_q <= branch_jump_set_done_d;
    end
  end

  // the _raw signals from the state machine may be asserted for multiple cycles when
  // instr_executing_spec is asserted and instr_executing is not asserted. This may occur where
  // a memory error is seen or a there are outstanding memory accesses (indicate a load or store is
  // in the WB stage). The branch or jump speculatively begins the fetch but is held back from
  // completing until it is certain the outstanding access hasn't seen a memory error. This logic
  // ensures only the first cycle of a branch or jump set is sent to the controller to prevent
  // needless extra IF flushes and fetches.
  assign jump_set        = jump_set_raw        & ~branch_jump_set_done_q;
  assign branch_set      = branch_set_raw      & ~branch_jump_set_done_q;

  // Branch condition is calculated in the first cycle and flopped for use in the second cycle
  // (only used in fixed time execution mode to determine branch destination).
  if (DataIndTiming) begin : g_sec_branch_taken
    // SEC_CM: CORE.DATA_REG_SW.SCA
    logic branch_taken_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        branch_taken_q <= 1'b0;
      end else begin
        branch_taken_q <= branch_decision_i;
      end
    end

    assign branch_taken = ~data_ind_timing_i | branch_taken_q;

  end else begin : g_nosec_branch_taken

    // Signal unused without fixed time execution mode - only taken branches will trigger
    // branch_set_raw
    assign branch_taken = 1'b1;

  end

  // Holding branch_set/jump_set high for more than one cycle should not cause a functional issue.
  // However it could generate needless prefetch buffer flushes and instruction fetches. The ID/EX
  // designs ensures that this never happens for non-predicted branches.
  `ASSERT(NeverDoubleBranch, branch_set & ~instr_bp_taken_i |=> ~branch_set)
  `ASSERT(NeverDoubleJump, jump_set & ~instr_bp_taken_i |=> ~jump_set)

  //////////////////////////////
  // Branch not-taken address //
  //////////////////////////////

  if (BranchPredictor) begin : g_calc_nt_addr
    assign nt_branch_addr_o = pc_id_i + (instr_is_compressed_i ? 32'd2 : 32'd4);
  end else begin : g_n_calc_nt_addr
    assign nt_branch_addr_o = 32'd0;
  end

  ///////////////
  // ID-EX FSM //
  ///////////////

  typedef enum logic { FIRST_CYCLE, MULTI_CYCLE } id_fsm_e;
  id_fsm_e id_fsm_q, id_fsm_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : id_pipeline_reg
    if (!rst_ni) begin
      id_fsm_q <= FIRST_CYCLE;
    end else if (instr_executing) begin
      id_fsm_q <= id_fsm_d;
    end
  end

  // ID/EX stage can be in two states, FIRST_CYCLE and MULTI_CYCLE. An instruction enters
  // MULTI_CYCLE if it requires multiple cycles to complete regardless of stalls and other
  // considerations. An instruction may be held in FIRST_CYCLE if it's unable to begin executing
  // (this is controlled by instr_executing).

  always_comb begin
    id_fsm_d                = id_fsm_q;
    rf_we_raw               = rf_we_dec;
    stall_multdiv           = 1'b0;
    stall_jump              = 1'b0;
    stall_branch            = 1'b0;
    stall_alu               = 1'b0;
    branch_set_raw_d        = 1'b0;
    branch_not_set          = 1'b0;
    jump_set_raw            = 1'b0;
    perf_branch_o           = 1'b0;

    if (instr_executing_spec) begin
      unique case (id_fsm_q)
        FIRST_CYCLE: begin
          unique case (1'b1)
            lsu_req_dec: begin
              if (!WritebackStage) begin
                // LSU operation
                id_fsm_d    = MULTI_CYCLE;
              end else begin
                if(~lsu_req_done_i) begin
                  id_fsm_d  = MULTI_CYCLE;
                end
              end
            end
            multdiv_en_dec: begin
              // MUL or DIV operation
              if (~ex_valid_i) begin
                // When single-cycle multiply is configured mul can finish in the first cycle so
                // only enter MULTI_CYCLE state if a result isn't immediately available
                id_fsm_d      = MULTI_CYCLE;
                rf_we_raw     = 1'b0;
                stall_multdiv = 1'b1;
              end
            end
            branch_in_dec: begin
              // cond branch operation
              // All branches take two cycles in fixed time execution mode, regardless of branch
              // condition.
              // SEC_CM: CORE.DATA_REG_SW.SCA
              id_fsm_d         = (data_ind_timing_i || (!BranchTargetALU && branch_decision_i)) ?
                                     MULTI_CYCLE : FIRST_CYCLE;
              stall_branch     = (~BranchTargetALU & branch_decision_i) | data_ind_timing_i;
              branch_set_raw_d = (branch_decision_i | data_ind_timing_i);

              if (BranchPredictor) begin
                branch_not_set = ~branch_decision_i;
              end

              perf_branch_o = 1'b1;
            end
            jump_in_dec: begin
              // uncond branch operation
              // BTALU means jumps only need one cycle
              id_fsm_d      = BranchTargetALU ? FIRST_CYCLE : MULTI_CYCLE;
              stall_jump    = ~BranchTargetALU;
              jump_set_raw  = jump_set_dec;
            end
            alu_multicycle_dec: begin
              stall_alu     = 1'b1;
              id_fsm_d      = MULTI_CYCLE;
              rf_we_raw     = 1'b0;
            end
            default: begin
              id_fsm_d      = FIRST_CYCLE;
            end
          endcase
        end

        MULTI_CYCLE: begin
          if(multdiv_en_dec) begin
            rf_we_raw       = rf_we_dec & ex_valid_i;
          end

          if (multicycle_done & ready_wb_i) begin
            id_fsm_d        = FIRST_CYCLE;
          end else begin
            stall_multdiv   = multdiv_en_dec;
            stall_branch    = branch_in_dec;
            stall_jump      = jump_in_dec;
          end
        end

        default: begin
          id_fsm_d          = FIRST_CYCLE;
        end
      endcase
    end
  end

  // Note for the two-stage configuration ready_wb_i is always set
  assign multdiv_ready_id_o = ready_wb_i;

  `ASSERT(StallIDIfMulticycle, (id_fsm_q == FIRST_CYCLE) & (id_fsm_d == MULTI_CYCLE) |-> stall_id)


  // Stall ID/EX stage for reason that relates to instruction in ID/EX, update assertion below if
  // modifying this.
  assign stall_id = stall_ld_hz | stall_mem | stall_multdiv | stall_jump | stall_branch |
                      stall_alu;

  // Generally illegal instructions have no reason to stall, however they must still stall waiting
  // for outstanding memory requests so exceptions related to them take priority over the illegal
  // instruction exception.
  `ASSERT(IllegalInsnStallMustBeMemStall, illegal_insn_o & stall_id |-> stall_mem &
    ~(stall_ld_hz | stall_multdiv | stall_jump | stall_branch | stall_alu))

  assign instr_done = ~stall_id & ~flush_id & instr_executing;

  // Signal instruction in ID is in it's first cycle. It can remain in its
  // first cycle if it is stalled.
  assign instr_first_cycle      = instr_valid_i & (id_fsm_q == FIRST_CYCLE);
  // Used by RVFI to know when to capture register read data
  // Used by ALU to access RS3 if ternary instruction.
  assign instr_first_cycle_id_o = instr_first_cycle;

  if (WritebackStage) begin : gen_stall_mem
    // Register read address matches write address in WB
    logic rf_rd_a_wb_match;
    logic rf_rd_b_wb_match;
    // Hazard between registers being read and written
    logic rf_rd_a_hz;
    logic rf_rd_b_hz;

    logic outstanding_memory_access;

    logic instr_kill;

    assign multicycle_done = lsu_req_dec ? ~stall_mem : ex_valid_i;

    // Is a memory access ongoing that isn't finishing this cycle
    assign outstanding_memory_access = (outstanding_load_wb_i | outstanding_store_wb_i) &
                                       ~lsu_resp_valid_i;

    // Can start a new memory access if any previous one has finished or is finishing
    assign data_req_allowed = ~outstanding_memory_access;

    // Instruction won't execute because:
    // - There is a pending exception in writeback
    //   The instruction in ID/EX will be flushed and the core will jump to an exception handler
    // - The controller isn't running instructions
    //   This either happens in preparation for a flush and jump to an exception handler e.g. in
    //   response to an IRQ or debug request or whilst the core is sleeping or resetting/fetching
    //   first instruction in which case any valid instruction in ID/EX should be ignored.
    // - There was an error on instruction fetch
    assign instr_kill = instr_fetch_err_i |
                        wb_exception      |
                        id_exception      |
                        ~controller_run;

    // With writeback stage instructions must be prevented from executing if there is:
    // - A load hazard
    // - A pending memory access
    //   If it receives an error response this results in a precise exception from WB so ID/EX
    //   instruction must not execute until error response is known).
    // - A load/store error
    //   This will cause a precise exception for the instruction in WB so ID/EX instruction must not
    //   execute
    //
    // instr_executing_spec is a speculative signal. It indicates an instruction can execute
    // assuming there are no exceptions from writeback and any outstanding memory access won't
    // receive an error. It is required so branch and jump requests don't factor in an incoming dmem
    // error (that in turn would factor directly into imem requests leading to a feedthrough path).
    //
    // instr_executing is the full signal, it will only allow execution once any potential
    // exceptions from writeback have been resolved.
    assign instr_executing_spec = instr_valid_i      &
                                  ~instr_fetch_err_i &
                                  controller_run     &
                                  ~stall_ld_hz;

    assign instr_executing = instr_valid_i              &
                             ~instr_kill                &
                             ~stall_ld_hz               &
                             ~outstanding_memory_access;

    `ASSERT(IbexExecutingSpecIfExecuting, instr_executing |-> instr_executing_spec)

    `ASSERT(IbexStallIfValidInstrNotExecuting,
      instr_valid_i & ~instr_kill & ~instr_executing |-> stall_id)

    `ASSERT(IbexCannotRetireWithPendingExceptions,
      instr_done |-> ~(wb_exception | outstanding_memory_access))

    // Stall for reasons related to memory:
    // * There is an outstanding memory access that won't resolve this cycle (need to wait to allow
    //   precise exceptions)
    // * There is a load/store request not being granted or which is unaligned and waiting to issue
    //   a second request (needs to stay in ID for the address calculation)
    assign stall_mem = instr_valid_i &
                       (outstanding_memory_access | (lsu_req_dec & ~lsu_req_done_i));

    // If we stall a load in ID for any reason, it must not make an LSU request
    // (otherwide we might issue two requests for the same instruction)
    `ASSERT(IbexStallMemNoRequest,
      instr_valid_i & lsu_req_dec & ~instr_done |-> ~lsu_req_done_i)

    assign rf_rd_a_wb_match = (rf_waddr_wb_i == rf_raddr_a_o) & |rf_raddr_a_o;
    assign rf_rd_b_wb_match = (rf_waddr_wb_i == rf_raddr_b_o) & |rf_raddr_b_o;

    assign rf_rd_a_wb_match_o = rf_rd_a_wb_match;
    assign rf_rd_b_wb_match_o = rf_rd_b_wb_match;

    // If instruction is reading register that load will be writing stall in
    // ID until load is complete. No need to stall when reading zero register.
    assign rf_rd_a_hz = rf_rd_a_wb_match & rf_ren_a;
    assign rf_rd_b_hz = rf_rd_b_wb_match & rf_ren_b;

    // If instruction is read register that writeback is writing forward writeback data to read
    // data. Note this doesn't factor in load data as it arrives too late, such hazards are
    // resolved via a stall (see above).
    assign rf_rdata_a_fwd = rf_rd_a_wb_match & rf_write_wb_i ? rf_wdata_fwd_wb_i : rf_rdata_a_i;
    assign rf_rdata_b_fwd = rf_rd_b_wb_match & rf_write_wb_i ? rf_wdata_fwd_wb_i : rf_rdata_b_i;

    assign stall_ld_hz = outstanding_load_wb_i & (rf_rd_a_hz | rf_rd_b_hz);

    assign instr_type_wb_o = ~lsu_req_dec ? WB_INSTR_OTHER :
                              lsu_we      ? WB_INSTR_STORE :
                                            WB_INSTR_LOAD;

    assign instr_id_done_o = en_wb_o & ready_wb_i;

    // Stall ID/EX as instruction in ID/EX cannot proceed to writeback yet
    assign stall_wb = en_wb_o & ~ready_wb_i;

    assign perf_dside_wait_o = instr_valid_i & ~instr_kill &
                               (outstanding_memory_access | stall_ld_hz);
  end else begin : gen_no_stall_mem

    assign multicycle_done = lsu_req_dec ? lsu_resp_valid_i : ex_valid_i;

    assign data_req_allowed = instr_first_cycle;

    // Without Writeback Stage always stall the first cycle of a load/store.
    // Then stall until it is complete
    assign stall_mem = instr_valid_i & (lsu_req_dec & (~lsu_resp_valid_i | instr_first_cycle));

    // No load hazards without Writeback Stage
    assign stall_ld_hz   = 1'b0;

    // Without writeback stage any valid instruction that hasn't seen an error will execute
    assign instr_executing_spec = instr_valid_i & ~instr_fetch_err_i & controller_run;
    assign instr_executing = instr_executing_spec;

    `ASSERT(IbexStallIfValidInstrNotExecuting,
      instr_valid_i & ~instr_fetch_err_i & ~instr_executing & controller_run |-> stall_id)

    // No data forwarding without writeback stage so always take source register data direct from
    // register file
    assign rf_rdata_a_fwd = rf_rdata_a_i;
    assign rf_rdata_b_fwd = rf_rdata_b_i;

    assign rf_rd_a_wb_match_o = 1'b0;
    assign rf_rd_b_wb_match_o = 1'b0;

    // Unused Writeback stage only IO & wiring
    // Assign inputs and internal wiring to unused signals to satisfy lint checks
    // Tie-off outputs to constant values
    logic unused_data_req_done_ex;
    logic [4:0] unused_rf_waddr_wb;
    logic unused_rf_write_wb;
    logic unused_outstanding_load_wb;
    logic unused_outstanding_store_wb;
    logic unused_wb_exception;
    logic [31:0] unused_rf_wdata_fwd_wb;
    logic unused_id_exception;

    assign unused_data_req_done_ex     = lsu_req_done_i;
    assign unused_rf_waddr_wb          = rf_waddr_wb_i;
    assign unused_rf_write_wb          = rf_write_wb_i;
    assign unused_outstanding_load_wb  = outstanding_load_wb_i;
    assign unused_outstanding_store_wb = outstanding_store_wb_i;
    assign unused_wb_exception         = wb_exception;
    assign unused_rf_wdata_fwd_wb      = rf_wdata_fwd_wb_i;
    assign unused_id_exception         = id_exception;

    assign instr_type_wb_o = WB_INSTR_OTHER;
    assign stall_wb        = 1'b0;

    assign perf_dside_wait_o = instr_executing & lsu_req_dec & ~lsu_resp_valid_i;

    assign instr_id_done_o = instr_done;
  end

  // Signal which instructions to count as retired in minstret, all traps along with ebrk and
  // ecall instructions are not counted.
  assign instr_perf_count_id_o = ~ebrk_insn & ~ecall_insn_dec & ~illegal_insn_dec &
      ~illegal_csr_insn_i & ~instr_fetch_err_i;

  // An instruction is ready to move to the writeback stage (or retire if there is no writeback
  // stage)
  assign en_wb_o = instr_done;

  assign perf_mul_wait_o = stall_multdiv & mult_en_dec;
  assign perf_div_wait_o = stall_multdiv & div_en_dec;

  //////////
  // FCOV //
  //////////

  `DV_FCOV_SIGNAL_GEN_IF(logic, rf_rd_wb_hz,
    (gen_stall_mem.rf_rd_a_hz | gen_stall_mem.rf_rd_b_hz) & instr_valid_i, WritebackStage)
  `DV_FCOV_SIGNAL(logic, branch_taken,
    instr_executing & (id_fsm_q == FIRST_CYCLE) & branch_decision_i)
  `DV_FCOV_SIGNAL(logic, branch_not_taken,
    instr_executing & (id_fsm_q == FIRST_CYCLE) & ~branch_decision_i)

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT_KNOWN_IF(IbexAluOpMuxSelKnown, alu_op_a_mux_sel, instr_valid_i)
  `ASSERT(IbexAluAOpMuxSelValid, instr_valid_i |-> alu_op_a_mux_sel inside {
      OP_A_REG_A,
      OP_A_FWD,
      OP_A_CURRPC,
      OP_A_IMM})
  `ASSERT_KNOWN_IF(IbexBTAluAOpMuxSelKnown, bt_a_mux_sel, instr_valid_i)
  `ASSERT(IbexBTAluAOpMuxSelValid, instr_valid_i |-> bt_a_mux_sel inside {
      OP_A_REG_A,
      OP_A_CURRPC})
  `ASSERT_KNOWN_IF(IbexBTAluBOpMuxSelKnown, bt_b_mux_sel, instr_valid_i)
  `ASSERT(IbexBTAluBOpMuxSelValid, instr_valid_i |-> bt_b_mux_sel inside {
      IMM_B_I,
      IMM_B_B,
      IMM_B_J,
      IMM_B_INCR_PC})
  `ASSERT(IbexRegfileWdataSelValid, instr_valid_i |-> rf_wdata_sel inside {
      RF_WD_EX,
      RF_WD_CSR})
  `ASSERT_KNOWN(IbexWbStateKnown, id_fsm_q)

  // Branch decision must be valid when jumping.
  `ASSERT_KNOWN_IF(IbexBranchDecisionValid, branch_decision_i,
      instr_valid_i && !(illegal_csr_insn_i || instr_fetch_err_i))

  // Instruction delivered to ID stage can not contain X.
  `ASSERT_KNOWN_IF(IbexIdInstrKnown, instr_rdata_i,
      instr_valid_i && !(illegal_c_insn_i || instr_fetch_err_i))

  // Instruction delivered to ID stage can not contain X.
  `ASSERT_KNOWN_IF(IbexIdInstrALUKnown, instr_rdata_alu_i,
      instr_valid_i && !(illegal_c_insn_i || instr_fetch_err_i))

  // Multicycle enable signals must be unique.
  `ASSERT(IbexMulticycleEnableUnique,
      $onehot0({lsu_req_dec, multdiv_en_dec, branch_in_dec, jump_in_dec}))

  // Duplicated instruction flops must match
  // === as DV environment can produce instructions with Xs in, so must use precise match that
  // includes Xs
  `ASSERT(IbexDuplicateInstrMatch, instr_valid_i |-> instr_rdata_i === instr_rdata_alu_i)

  `ifdef CHECK_MISALIGNED
  `ASSERT(IbexMisalignedMemoryAccess, !lsu_addr_incr_req_i)
  `endif

endmodule
