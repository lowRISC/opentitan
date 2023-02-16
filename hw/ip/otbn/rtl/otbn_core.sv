// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OpenTitan Big Number Accelerator (OTBN) Core
 *
 * This module is the top-level of the OTBN processing core.
 */
// Below countermeasure (no data dependent control flow in OTBN ISA) is inherent to the design and
// has no directly associated RTL
// SEC_CM: CTRL_FLOW.SCA
module otbn_core
  import otbn_pkg::*;
#(
  // Register file implementation selection, see otbn_pkg.sv.
  parameter regfile_e RegFile = RegFileFF,

  // Size of the instruction memory, in bytes
  parameter int ImemSizeByte = 4096,
  // Size of the data memory, in bytes
  parameter int DmemSizeByte = 4096,

  // Default seed for URND PRNG
  parameter urnd_prng_seed_t RndCnstUrndPrngSeed = RndCnstUrndPrngSeedDefault,

  // Disable URND reseed and advance when not in use. Useful for SCA only.
  parameter bit SecMuteUrnd = 1'b0,
  parameter bit SecSkipUrndReseedAtStart = 1'b0,

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte),
  localparam int DmemAddrWidth = prim_util_pkg::vbits(DmemSizeByte)
) (
  input logic clk_i,
  input logic rst_ni,

  input  logic start_i,   // start the operation
  output logic done_o,    // operation done
  output logic locking_o, // The core is in or is entering the locked state
  output logic secure_wipe_running_o, // the core is securely wiping its internal state

  output core_err_bits_t err_bits_o,  // valid when done_o is asserted
  output logic           recoverable_err_o,

  // Instruction memory (IMEM)
  output logic                     imem_req_o,
  output logic [ImemAddrWidth-1:0] imem_addr_o,
  input  logic [38:0]              imem_rdata_i,
  input  logic                     imem_rvalid_i,

  // Data memory (DMEM)
  output logic                        dmem_req_o,
  output logic                        dmem_write_o,
  output logic [DmemAddrWidth-1:0]    dmem_addr_o,
  output logic [ExtWLEN-1:0]          dmem_wdata_o,
  output logic [ExtWLEN-1:0]          dmem_wmask_o,
  output logic [BaseWordsPerWLEN-1:0] dmem_rmask_o,
  input  logic [ExtWLEN-1:0]          dmem_rdata_i,
  input  logic                        dmem_rvalid_i,
  input  logic                        dmem_rerror_i,

  // Entropy distribution network (EDN) connections
  // One for RND, the other for URND
  output logic                    edn_rnd_req_o,
  input  logic                    edn_rnd_ack_i,
  input  logic [EdnDataWidth-1:0] edn_rnd_data_i,
  input  logic                    edn_rnd_fips_i,
  input  logic                    edn_rnd_err_i,

  output logic                    edn_urnd_req_o,
  input  logic                    edn_urnd_ack_i,
  input  logic [EdnDataWidth-1:0] edn_urnd_data_i,

  output logic [31:0] insn_cnt_o,
  input  logic        insn_cnt_clear_i,

  output logic         mems_sec_wipe_o,          // Request secure wipe for imem and dmem
  input  logic         req_sec_wipe_urnd_keys_i, // Request URND bits for temporary scramble keys.
                                                 // Keys below are valid cycle after request.
  output logic [127:0] dmem_sec_wipe_urnd_key_o, // URND bits to give temporary dmem scramble key
  output logic [127:0] imem_sec_wipe_urnd_key_o, // URND bits to give temporary imem scramble key

  // Indicates an incoming escalation from some fatal error at the level above. The core needs to
  // halt and then enter a locked state.
  input prim_mubi_pkg::mubi4_t escalate_en_i,

  // Indicates an incoming RMA request. The core needs to halt, trigger a secure wipe immediately
  // and then enter a locked state.
  input  prim_mubi_pkg::mubi4_t rma_req_i,
  output prim_mubi_pkg::mubi4_t rma_ack_o,

  // When set software errors become fatal errors.
  input logic software_errs_fatal_i,

  input logic [1:0]                       sideload_key_shares_valid_i,
  input logic [1:0][SideloadKeyWidth-1:0] sideload_key_shares_i
);
  import prim_mubi_pkg::*;

  // Create a lint error to reduce the risk of accidentally enabling this feature.
  `ASSERT_STATIC_LINT_ERROR(OtbnSecMuteUrndNonDefault, SecMuteUrnd == 0)

  // Fetch request (the next instruction)
  logic [ImemAddrWidth-1:0] insn_fetch_req_addr;
  logic                     insn_fetch_req_valid;
  logic                     insn_fetch_req_valid_raw;

  // Fetch response (the current instruction before it is decoded)
  logic                     insn_fetch_resp_valid;
  logic [ImemAddrWidth-1:0] insn_fetch_resp_addr;
  logic [31:0]              insn_fetch_resp_data;
  logic                     insn_fetch_resp_clear;
  logic                     insn_fetch_err;
  logic                     insn_addr_err;

  rf_predec_bignum_t        rf_predec_bignum;
  alu_predec_bignum_t       alu_predec_bignum;
  ctrl_flow_predec_t        ctrl_flow_predec;
  logic [ImemAddrWidth-1:0] ctrl_flow_target_predec;
  ispr_predec_bignum_t      ispr_predec_bignum;
  mac_predec_bignum_t       mac_predec_bignum;
  logic                     lsu_addr_en_predec;

  logic [NWdr-1:0] rf_bignum_rd_a_indirect_onehot;
  logic [NWdr-1:0] rf_bignum_rd_b_indirect_onehot;
  logic [NWdr-1:0] rf_bignum_wr_indirect_onehot;
  logic            rf_bignum_indirect_en;

  // The currently executed instruction.
  logic                     insn_valid;
  logic                     insn_illegal;
  logic [ImemAddrWidth-1:0] insn_addr;
  insn_dec_base_t           insn_dec_base;
  insn_dec_bignum_t         insn_dec_bignum;
  insn_dec_shared_t         insn_dec_shared;

  logic [4:0]               rf_base_wr_addr;
  logic [4:0]               rf_base_wr_addr_ctrl;
  logic                     rf_base_wr_en;
  logic                     rf_base_wr_en_ctrl;
  logic                     rf_base_wr_commit;
  logic                     rf_base_wr_commit_ctrl;
  logic [31:0]              rf_base_wr_data_no_intg;
  logic [31:0]              rf_base_wr_data_no_intg_ctrl;
  logic [BaseIntgWidth-1:0] rf_base_wr_data_intg;
  logic                     rf_base_wr_data_intg_sel, rf_base_wr_data_intg_sel_ctrl;
  logic [4:0]               rf_base_rd_addr_a;
  logic                     rf_base_rd_en_a;
  logic [BaseIntgWidth-1:0] rf_base_rd_data_a_intg;
  logic [4:0]               rf_base_rd_addr_b;
  logic                     rf_base_rd_en_b;
  logic [BaseIntgWidth-1:0] rf_base_rd_data_b_intg;
  logic                     rf_base_rd_commit;
  logic                     rf_base_call_stack_sw_err;
  logic                     rf_base_call_stack_hw_err;
  logic                     rf_base_intg_err;
  logic                     rf_base_spurious_we_err;

  alu_base_operation_t  alu_base_operation;
  alu_base_comparison_t alu_base_comparison;
  logic [31:0]          alu_base_operation_result;
  logic                 alu_base_comparison_result;

  logic                     lsu_load_req;
  logic                     lsu_store_req;
  insn_subset_e             lsu_req_subset;
  logic [DmemAddrWidth-1:0] lsu_addr;

  logic [BaseIntgWidth-1:0] lsu_base_wdata;
  logic [ExtWLEN-1:0]       lsu_bignum_wdata;

  logic [BaseIntgWidth-1:0] lsu_base_rdata;
  logic [ExtWLEN-1:0]       lsu_bignum_rdata;
  logic                     lsu_rdata_err;

  logic [WdrAw-1:0]   rf_bignum_wr_addr;
  logic [WdrAw-1:0]   rf_bignum_wr_addr_ctrl;
  logic [1:0]         rf_bignum_wr_en;
  logic [1:0]         rf_bignum_wr_en_ctrl;
  logic               rf_bignum_wr_commit;
  logic               rf_bignum_wr_commit_ctrl;
  logic [WLEN-1:0]    rf_bignum_wr_data_no_intg;
  logic [WLEN-1:0]    rf_bignum_wr_data_no_intg_ctrl;
  logic [ExtWLEN-1:0] rf_bignum_wr_data_intg;
  logic               rf_bignum_wr_data_intg_sel, rf_bignum_wr_data_intg_sel_ctrl;
  logic [WdrAw-1:0]   rf_bignum_rd_addr_a;
  logic               rf_bignum_rd_en_a;
  logic [ExtWLEN-1:0] rf_bignum_rd_data_a_intg;
  logic [WdrAw-1:0]   rf_bignum_rd_addr_b;
  logic               rf_bignum_rd_en_b;
  logic [ExtWLEN-1:0] rf_bignum_rd_data_b_intg;
  logic               rf_bignum_intg_err;
  logic               rf_bignum_spurious_we_err;

  alu_bignum_operation_t alu_bignum_operation;
  logic                  alu_bignum_operation_valid;
  logic                  alu_bignum_operation_commit;
  logic [WLEN-1:0]       alu_bignum_operation_result;
  logic                  alu_bignum_selection_flag;
  logic                  alu_bignum_reg_intg_violation_err;

  mac_bignum_operation_t mac_bignum_operation;
  logic [WLEN-1:0]       mac_bignum_operation_result;
  flags_t                mac_bignum_operation_flags;
  flags_t                mac_bignum_operation_flags_en;
  logic                  mac_bignum_en;
  logic                  mac_bignum_commit;
  logic                  mac_bignum_reg_intg_violation_err;

  ispr_e                       ispr_addr;
  logic [31:0]                 ispr_base_wdata;
  logic [BaseWordsPerWLEN-1:0] ispr_base_wr_en;
  logic [ExtWLEN-1:0]          ispr_bignum_wdata_intg;
  logic                        ispr_bignum_wr_en;
  logic                        ispr_wr_commit;
  logic [ExtWLEN-1:0]          ispr_rdata_intg;
  logic                        ispr_rd_en;
  logic [ExtWLEN-1:0]          ispr_acc_intg;
  logic [ExtWLEN-1:0]          ispr_acc_wr_data_intg;
  logic                        ispr_acc_wr_en;
  logic                        ispr_init;

  logic            rnd_req;
  logic            rnd_prefetch_req;
  logic            rnd_valid;
  logic [WLEN-1:0] rnd_data;
  logic            rnd_rep_err;
  logic            rnd_fips_err;

  logic            urnd_reseed_req;
  logic            urnd_reseed_ack;
  logic            urnd_reseed_err;
  logic            urnd_advance;
  logic            urnd_advance_start_stop_control;
  logic [WLEN-1:0] urnd_data;
  logic            urnd_all_zero;

  logic        controller_start;

  logic        state_reset;
  logic [31:0] insn_cnt;

  logic secure_wipe_req, secure_wipe_ack;

  logic sec_wipe_wdr_d, sec_wipe_wdr_q;
  logic sec_wipe_wdr_urnd_d, sec_wipe_wdr_urnd_q;
  logic sec_wipe_base;
  logic sec_wipe_base_urnd;
  logic [4:0] sec_wipe_addr, sec_wipe_wdr_addr_q;

  logic sec_wipe_acc_urnd;
  logic sec_wipe_mod_urnd;
  logic sec_wipe_zero;

  logic                     prefetch_en;
  logic                     prefetch_loop_active;
  logic [31:0]              prefetch_loop_iterations;
  logic [ImemAddrWidth:0]   prefetch_loop_end_addr;
  logic [ImemAddrWidth-1:0] prefetch_loop_jump_addr;

  mubi4_t               controller_fatal_escalate_en, controller_recov_escalate_en;
  mubi4_t               start_stop_escalate_en;
  controller_err_bits_t controller_err_bits;
  logic                 prefetch_ignore_errs;

  core_err_bits_t err_bits_q, err_bits_d;
  logic           mubi_err;

  logic start_stop_fatal_error;
  logic rf_bignum_predec_error, alu_bignum_predec_error, ispr_predec_error, mac_bignum_predec_error;
  logic controller_predec_error;
  logic rd_predec_error, predec_error;

  logic req_sec_wipe_urnd_keys_q;

  // Start stop control start OTBN execution when requested and deals with any pre start or post
  // stop actions.
  otbn_start_stop_control #(
    .SecMuteUrnd(SecMuteUrnd),
    .SecSkipUrndReseedAtStart(SecSkipUrndReseedAtStart)
  ) u_otbn_start_stop_control (
    .clk_i,
    .rst_ni,

    .start_i,
    .escalate_en_i(start_stop_escalate_en),
    .rma_req_i,
    .rma_ack_o,

    .controller_start_o(controller_start),

    .urnd_reseed_req_o (urnd_reseed_req),
    .urnd_reseed_ack_i (urnd_reseed_ack),
    .urnd_reseed_err_o (urnd_reseed_err),
    .urnd_advance_o    (urnd_advance_start_stop_control),

    .secure_wipe_req_i (secure_wipe_req),
    .secure_wipe_ack_o (secure_wipe_ack),
    .secure_wipe_running_o,
    .done_o,

    .sec_wipe_wdr_o      (sec_wipe_wdr_d),
    .sec_wipe_wdr_urnd_o (sec_wipe_wdr_urnd_d),
    .sec_wipe_base_o     (sec_wipe_base),
    .sec_wipe_base_urnd_o(sec_wipe_base_urnd),
    .sec_wipe_addr_o     (sec_wipe_addr),

    .sec_wipe_acc_urnd_o(sec_wipe_acc_urnd),
    .sec_wipe_mod_urnd_o(sec_wipe_mod_urnd),
    .sec_wipe_zero_o    (sec_wipe_zero),

    .ispr_init_o  (ispr_init),
    .state_reset_o(state_reset),
    .fatal_error_o(start_stop_fatal_error)
  );

  // Depending on its usage, the instruction address (program counter) is qualified by two valid
  // signals: insn_fetch_resp_valid (together with the undecoded instruction data), and insn_valid
  // for valid decoded (i.e. legal) instructions. Duplicate the signal in the source code for
  // consistent grouping of signals with their valid signal.
  assign insn_addr = insn_fetch_resp_addr;

  // Instruction fetch unit
  otbn_instruction_fetch #(
    .ImemSizeByte(ImemSizeByte)
  ) u_otbn_instruction_fetch (
    .clk_i,
    .rst_ni,

    // Instruction memory interface
    .imem_req_o,
    .imem_addr_o,
    .imem_rdata_i,
    .imem_rvalid_i,

    // Instruction to fetch
    .insn_fetch_req_addr_i     (insn_fetch_req_addr),
    .insn_fetch_req_valid_i    (insn_fetch_req_valid),
    .insn_fetch_req_valid_raw_i(insn_fetch_req_valid_raw),

    // Fetched instruction
    .insn_fetch_resp_addr_o (insn_fetch_resp_addr),
    .insn_fetch_resp_valid_o(insn_fetch_resp_valid),
    .insn_fetch_resp_data_o (insn_fetch_resp_data),
    .insn_fetch_resp_clear_i(insn_fetch_resp_clear),
    .insn_fetch_err_o       (insn_fetch_err),
    .insn_addr_err_o        (insn_addr_err),

    .rf_predec_bignum_o       (rf_predec_bignum),
    .alu_predec_bignum_o      (alu_predec_bignum),
    .ctrl_flow_predec_o       (ctrl_flow_predec),
    .ctrl_flow_target_predec_o(ctrl_flow_target_predec),
    .ispr_predec_bignum_o     (ispr_predec_bignum),
    .mac_predec_bignum_o      (mac_predec_bignum),
    .lsu_addr_en_predec_o     (lsu_addr_en_predec),

    .rf_bignum_rd_a_indirect_onehot_i(rf_bignum_rd_a_indirect_onehot),
    .rf_bignum_rd_b_indirect_onehot_i(rf_bignum_rd_b_indirect_onehot),
    .rf_bignum_wr_indirect_onehot_i  (rf_bignum_wr_indirect_onehot),
    .rf_bignum_indirect_en_i         (rf_bignum_indirect_en),

    .prefetch_en_i             (prefetch_en),
    .prefetch_loop_active_i    (prefetch_loop_active),
    .prefetch_loop_iterations_i(prefetch_loop_iterations),
    .prefetch_loop_end_addr_i  (prefetch_loop_end_addr),
    .prefetch_loop_jump_addr_i (prefetch_loop_jump_addr),
    .prefetch_ignore_errs_i    (prefetch_ignore_errs),

    .sec_wipe_wdr_en_i  (sec_wipe_wdr_d),
    .sec_wipe_wdr_addr_i(sec_wipe_addr)
  );

  // Instruction decoder
  otbn_decoder u_otbn_decoder (
    // The decoder is combinatorial; clk and rst are only used for assertions.
    .clk_i,
    .rst_ni,

    // Instruction to decode
    .insn_fetch_resp_data_i (insn_fetch_resp_data),
    .insn_fetch_resp_valid_i(insn_fetch_resp_valid),

    // Decoded instruction
    .insn_valid_o     (insn_valid),
    .insn_illegal_o   (insn_illegal),
    .insn_dec_base_o  (insn_dec_base),
    .insn_dec_bignum_o(insn_dec_bignum),
    .insn_dec_shared_o(insn_dec_shared)
  );

  // SEC_CM: CTRL.REDUN
  // ALU and MAC predecode is only relevant when there is a valid instruction, as without one it is
  // guaranteed there are no register reads (hence no sensitive data bits being fed into the blanked
  // data paths). RF and ISPR predecode must always be checked to ensure read and write data paths
  // are always correctly blanked.
  assign rd_predec_error = |{rf_predec_bignum.rf_ren_a,
                             rf_predec_bignum.rf_ren_b,
                             ispr_predec_bignum.ispr_rd_en} & ~insn_valid;

  assign predec_error =
    ((alu_bignum_predec_error | mac_bignum_predec_error | controller_predec_error) & insn_valid) |
     rf_bignum_predec_error                                                                      |
     ispr_predec_error                                                                           |
     rd_predec_error;

  // Controller: coordinate between functional units, prepare their inputs (e.g. by muxing between
  // operand sources), and post-process their outputs as needed.
  otbn_controller #(
    .ImemSizeByte(ImemSizeByte),
    .DmemSizeByte(DmemSizeByte)
  ) u_otbn_controller (
    .clk_i,
    .rst_ni,

    .start_i         (controller_start),
    .locking_o,
    .err_bit_clear_i (start_i),

    .fatal_escalate_en_i(controller_fatal_escalate_en),
    .recov_escalate_en_i(controller_recov_escalate_en),
    .rma_req_i,
    .err_bits_o         (controller_err_bits),
    .recoverable_err_o,

    // Next instruction selection (to instruction fetch)
    .insn_fetch_req_addr_o     (insn_fetch_req_addr),
    .insn_fetch_req_valid_o    (insn_fetch_req_valid),
    .insn_fetch_req_valid_raw_o(insn_fetch_req_valid_raw),
    .insn_fetch_resp_clear_o   (insn_fetch_resp_clear),

    // The current instruction
    .insn_valid_i  (insn_valid),
    .insn_illegal_i(insn_illegal),
    .insn_addr_i   (insn_addr),

    // Decoded instruction from decoder
    .insn_dec_base_i  (insn_dec_base),
    .insn_dec_bignum_i(insn_dec_bignum),
    .insn_dec_shared_i(insn_dec_shared),

    // To/from base register file
    .rf_base_wr_addr_o          (rf_base_wr_addr_ctrl),
    .rf_base_wr_en_o            (rf_base_wr_en_ctrl),
    .rf_base_wr_commit_o        (rf_base_wr_commit_ctrl),
    .rf_base_wr_data_no_intg_o  (rf_base_wr_data_no_intg_ctrl),
    .rf_base_wr_data_intg_o     (rf_base_wr_data_intg),
    .rf_base_wr_data_intg_sel_o (rf_base_wr_data_intg_sel_ctrl),
    .rf_base_rd_addr_a_o        (rf_base_rd_addr_a),
    .rf_base_rd_en_a_o          (rf_base_rd_en_a),
    .rf_base_rd_data_a_intg_i   (rf_base_rd_data_a_intg),
    .rf_base_rd_addr_b_o        (rf_base_rd_addr_b),
    .rf_base_rd_en_b_o          (rf_base_rd_en_b),
    .rf_base_rd_data_b_intg_i   (rf_base_rd_data_b_intg),
    .rf_base_rd_commit_o        (rf_base_rd_commit),
    .rf_base_call_stack_sw_err_i(rf_base_call_stack_sw_err),
    .rf_base_call_stack_hw_err_i(rf_base_call_stack_hw_err),

    // To/from bignum register file
    .rf_bignum_wr_addr_o         (rf_bignum_wr_addr_ctrl),
    .rf_bignum_wr_en_o           (rf_bignum_wr_en_ctrl),
    .rf_bignum_wr_commit_o       (rf_bignum_wr_commit_ctrl),
    .rf_bignum_wr_data_no_intg_o (rf_bignum_wr_data_no_intg_ctrl),
    .rf_bignum_wr_data_intg_o    (rf_bignum_wr_data_intg),
    .rf_bignum_wr_data_intg_sel_o(rf_bignum_wr_data_intg_sel_ctrl),
    .rf_bignum_rd_addr_a_o       (rf_bignum_rd_addr_a),
    .rf_bignum_rd_en_a_o         (rf_bignum_rd_en_a),
    .rf_bignum_rd_data_a_intg_i  (rf_bignum_rd_data_a_intg),
    .rf_bignum_rd_addr_b_o       (rf_bignum_rd_addr_b),
    .rf_bignum_rd_en_b_o         (rf_bignum_rd_en_b),
    .rf_bignum_rd_data_b_intg_i  (rf_bignum_rd_data_b_intg),
    .rf_bignum_intg_err_i        (rf_bignum_intg_err),
    .rf_bignum_spurious_we_err_i (rf_bignum_spurious_we_err),

    .rf_bignum_rd_a_indirect_onehot_o(rf_bignum_rd_a_indirect_onehot),
    .rf_bignum_rd_b_indirect_onehot_o(rf_bignum_rd_b_indirect_onehot),
    .rf_bignum_wr_indirect_onehot_o  (rf_bignum_wr_indirect_onehot),
    .rf_bignum_indirect_en_o         (rf_bignum_indirect_en),

    // To/from base ALU
    .alu_base_operation_o        (alu_base_operation),
    .alu_base_comparison_o       (alu_base_comparison),
    .alu_base_operation_result_i (alu_base_operation_result),
    .alu_base_comparison_result_i(alu_base_comparison_result),

    // To/from bignum ALU
    .alu_bignum_operation_o       (alu_bignum_operation),
    .alu_bignum_operation_valid_o (alu_bignum_operation_valid),
    .alu_bignum_operation_commit_o(alu_bignum_operation_commit),
    .alu_bignum_operation_result_i(alu_bignum_operation_result),
    .alu_bignum_selection_flag_i  (alu_bignum_selection_flag),

    // To/from bignum MAC
    .mac_bignum_operation_o       (mac_bignum_operation),
    .mac_bignum_operation_result_i(mac_bignum_operation_result),
    .mac_bignum_en_o              (mac_bignum_en),
    .mac_bignum_commit_o          (mac_bignum_commit),

    // To/from LSU (base and bignum)
    .lsu_load_req_o          (lsu_load_req),
    .lsu_store_req_o         (lsu_store_req),
    .lsu_req_subset_o        (lsu_req_subset),
    .lsu_addr_o              (lsu_addr),
    .lsu_addr_en_predec_i    (lsu_addr_en_predec),

    .lsu_base_wdata_o  (lsu_base_wdata),
    .lsu_bignum_wdata_o(lsu_bignum_wdata),

    .lsu_base_rdata_i  (lsu_base_rdata),
    .lsu_bignum_rdata_i(lsu_bignum_rdata),

    // Isprs read/write (base and bignum)
    .ispr_addr_o             (ispr_addr),
    .ispr_base_wdata_o       (ispr_base_wdata),
    .ispr_base_wr_en_o       (ispr_base_wr_en),
    .ispr_bignum_wdata_intg_o(ispr_bignum_wdata_intg),
    .ispr_bignum_wr_en_o     (ispr_bignum_wr_en),
    .ispr_wr_commit_o        (ispr_wr_commit),
    .ispr_rdata_intg_i       (ispr_rdata_intg),
    .ispr_rd_en_o            (ispr_rd_en),

    // RND interface
    .rnd_req_o         (rnd_req),
    .rnd_prefetch_req_o(rnd_prefetch_req),
    .rnd_valid_i       (rnd_valid),

    .urnd_reseed_err_i(urnd_reseed_err),

    // Secure wipe
    .secure_wipe_req_o     (secure_wipe_req),
    .secure_wipe_ack_i     (secure_wipe_ack),
    .sec_wipe_zero_i       (sec_wipe_zero),
    .secure_wipe_running_i (secure_wipe_running_o),

    .state_reset_i(state_reset),
    .insn_cnt_o   (insn_cnt),
    .insn_cnt_clear_i,
    .mems_sec_wipe_o,

    .software_errs_fatal_i,

    .sideload_key_shares_valid_i,

    .prefetch_en_o             (prefetch_en),
    .prefetch_loop_active_o    (prefetch_loop_active),
    .prefetch_loop_iterations_o(prefetch_loop_iterations),
    .prefetch_loop_end_addr_o  (prefetch_loop_end_addr),
    .prefetch_loop_jump_addr_o (prefetch_loop_jump_addr),
    .prefetch_ignore_errs_o    (prefetch_ignore_errs),

    .ctrl_flow_predec_i       (ctrl_flow_predec),
    .ctrl_flow_target_predec_i(ctrl_flow_target_predec),
    .predec_error_o           (controller_predec_error)
  );

  `ASSERT(InsnDataStableInStall, u_otbn_controller.state_q == OtbnStateStall |->
                                 insn_fetch_resp_data == $past(insn_fetch_resp_data))

  // Spot the fatal error bits from the controller
  logic controller_fatal_err;
  assign controller_fatal_err = |{controller_err_bits.fatal_software,
                                  controller_err_bits.bad_internal_state,
                                  controller_err_bits.reg_intg_violation};

  logic non_controller_reg_intg_violation;
  assign non_controller_reg_intg_violation =
      |{alu_bignum_reg_intg_violation_err, mac_bignum_reg_intg_violation_err, rf_base_intg_err};


  // Generate an err_bits output by combining errors from all the blocks in otbn_core
  assign err_bits_d = '{
    fatal_software:      controller_err_bits.fatal_software,
    bad_internal_state:  |{controller_err_bits.bad_internal_state,
                           start_stop_fatal_error,
                           urnd_all_zero,
                           predec_error,
                           insn_addr_err,
                           rf_base_spurious_we_err,
                           mubi_err},
    reg_intg_violation:  |{controller_err_bits.reg_intg_violation,
                           non_controller_reg_intg_violation},
    dmem_intg_violation: lsu_rdata_err,
    imem_intg_violation: insn_fetch_err,
    rnd_fips_chk_fail:   rnd_fips_err,
    rnd_rep_chk_fail:    rnd_rep_err,
    key_invalid:         controller_err_bits.key_invalid,
    loop:                controller_err_bits.loop,
    illegal_insn:        controller_err_bits.illegal_insn,
    call_stack:          controller_err_bits.call_stack,
    bad_insn_addr:       controller_err_bits.bad_insn_addr,
    bad_data_addr:       controller_err_bits.bad_data_addr
  };

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      err_bits_q <= '0;
    end else begin
      if (start_i && !locking_o) begin
        err_bits_q <= '0;
      end else begin
        err_bits_q <= err_bits_q | err_bits_d;
      end
    end
  end
  assign err_bits_o = err_bits_q | err_bits_d;

  // Pass an "escalation" signal down to the controller by ORing in error signals from the other
  // modules in otbn_core. Note that each error signal except escalate_en_i that appears here also
  // appears somewhere in err_bits_o above (checked in ErrBitsIfControllerEscalate_A)
  assign controller_fatal_escalate_en =
      mubi4_or_hi(escalate_en_i,
                  mubi4_bool_to_mubi(|{start_stop_fatal_error, urnd_all_zero, predec_error,
                                       rf_base_intg_err, rf_base_spurious_we_err, lsu_rdata_err,
                                       insn_fetch_err, non_controller_reg_intg_violation,
                                       insn_addr_err}));

  assign controller_recov_escalate_en =
      mubi4_bool_to_mubi(|{rnd_rep_err, rnd_fips_err});

  // Similarly for the start/stop controller
  assign start_stop_escalate_en =
      mubi4_or_hi(escalate_en_i,
                  mubi4_bool_to_mubi(|{urnd_all_zero, rf_base_intg_err, rf_base_spurious_we_err,
                                       predec_error, lsu_rdata_err, insn_fetch_err,
                                       controller_fatal_err, insn_addr_err}));

  // Signal error if MuBi input signals take on invalid values as this means something bad is
  // happening. The explicit error detection is required as the mubi4_or_hi operations above
  // might mask invalid values depending on other input operands.
  assign mubi_err = mubi4_test_invalid(escalate_en_i);

  assign insn_cnt_o = insn_cnt;

  // Load store unit: read and write data from data memory
  otbn_lsu u_otbn_lsu (
    .clk_i,
    .rst_ni,

    // Data memory interface
    .dmem_req_o,
    .dmem_write_o,
    .dmem_addr_o,
    .dmem_wdata_o,
    .dmem_wmask_o,
    .dmem_rmask_o,
    .dmem_rdata_i,
    .dmem_rvalid_i,
    .dmem_rerror_i,

    .lsu_load_req_i  (lsu_load_req),
    .lsu_store_req_i (lsu_store_req),
    .lsu_req_subset_i(lsu_req_subset),
    .lsu_addr_i      (lsu_addr),

    .lsu_base_wdata_i  (lsu_base_wdata),
    .lsu_bignum_wdata_i(lsu_bignum_wdata),

    .lsu_base_rdata_o  (lsu_base_rdata),
    .lsu_bignum_rdata_o(lsu_bignum_rdata),
    .lsu_rdata_err_o   (lsu_rdata_err)
  );

  // Base Instruction Subset =======================================================================

  otbn_rf_base #(
    .RegFile(RegFile)
  ) u_otbn_rf_base (
    .clk_i,
    .rst_ni,

    .state_reset_i         (state_reset),
    .sec_wipe_stack_reset_i(sec_wipe_zero),

    .wr_addr_i         (rf_base_wr_addr),
    .wr_en_i           (rf_base_wr_en),
    .wr_data_no_intg_i (rf_base_wr_data_no_intg),
    .wr_data_intg_i    (rf_base_wr_data_intg),
    .wr_data_intg_sel_i(rf_base_wr_data_intg_sel),
    .wr_commit_i       (rf_base_wr_commit),

    .rd_addr_a_i     (rf_base_rd_addr_a),
    .rd_en_a_i       (rf_base_rd_en_a),
    .rd_data_a_intg_o(rf_base_rd_data_a_intg),
    .rd_addr_b_i     (rf_base_rd_addr_b),
    .rd_en_b_i       (rf_base_rd_en_b),
    .rd_data_b_intg_o(rf_base_rd_data_b_intg),
    .rd_commit_i     (rf_base_rd_commit),

    .call_stack_sw_err_o(rf_base_call_stack_sw_err),
    .call_stack_hw_err_o(rf_base_call_stack_hw_err),
    .intg_err_o         (rf_base_intg_err),
    .spurious_we_err_o  (rf_base_spurious_we_err)
  );

  assign rf_base_wr_addr         = sec_wipe_base ? sec_wipe_addr : rf_base_wr_addr_ctrl;
  assign rf_base_wr_en           = sec_wipe_base ? 1'b1          : rf_base_wr_en_ctrl;
  assign rf_base_wr_commit       = sec_wipe_base ? 1'b1          : rf_base_wr_commit_ctrl;

  // Write data to Base RF
  always_comb begin
    if (sec_wipe_base) begin
      // Wipe the Base RF with either random numbers or zeroes.
      if (sec_wipe_base_urnd) begin
        rf_base_wr_data_no_intg = urnd_data[31:0];
      end else begin
        rf_base_wr_data_no_intg = 32'b0;
      end
      rf_base_wr_data_intg_sel = 0;
    end else begin
      rf_base_wr_data_no_intg = rf_base_wr_data_no_intg_ctrl;
      rf_base_wr_data_intg_sel = rf_base_wr_data_intg_sel_ctrl;
    end
  end

  otbn_alu_base u_otbn_alu_base (
    .clk_i,
    .rst_ni,

    .operation_i        (alu_base_operation),
    .comparison_i       (alu_base_comparison),
    .operation_result_o (alu_base_operation_result),
    .comparison_result_o(alu_base_comparison_result)
  );

  otbn_rf_bignum #(
    .RegFile(RegFile)
  ) u_otbn_rf_bignum (
    .clk_i,
    .rst_ni,

    .wr_addr_i         (rf_bignum_wr_addr),
    .wr_en_i           (rf_bignum_wr_en),
    .wr_commit_i       (rf_bignum_wr_commit),
    .wr_data_no_intg_i (rf_bignum_wr_data_no_intg),
    .wr_data_intg_i    (rf_bignum_wr_data_intg),
    .wr_data_intg_sel_i(rf_bignum_wr_data_intg_sel),

    .rd_addr_a_i     (rf_bignum_rd_addr_a),
    .rd_en_a_i       (rf_bignum_rd_en_a),
    .rd_data_a_intg_o(rf_bignum_rd_data_a_intg),
    .rd_addr_b_i     (rf_bignum_rd_addr_b),
    .rd_en_b_i       (rf_bignum_rd_en_b),
    .rd_data_b_intg_o(rf_bignum_rd_data_b_intg),

    .intg_err_o(rf_bignum_intg_err),

    .rf_predec_bignum_i(rf_predec_bignum),
    .predec_error_o    (rf_bignum_predec_error),

    .spurious_we_err_o(rf_bignum_spurious_we_err)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      sec_wipe_wdr_q <= 1'b0;
    end else begin
      sec_wipe_wdr_q <= sec_wipe_wdr_d;
    end
  end

  always_ff @(posedge clk_i) begin
    if (sec_wipe_wdr_d) begin
      sec_wipe_wdr_addr_q <= sec_wipe_addr;
      sec_wipe_wdr_urnd_q <= sec_wipe_wdr_urnd_d;
    end
  end

  assign rf_bignum_wr_addr   = sec_wipe_wdr_q ? sec_wipe_wdr_addr_q : rf_bignum_wr_addr_ctrl;
  assign rf_bignum_wr_en     = sec_wipe_wdr_q ? 2'b11               : rf_bignum_wr_en_ctrl;
  assign rf_bignum_wr_commit = sec_wipe_wdr_q ? 1'b1                : rf_bignum_wr_commit_ctrl;

  // Write data to WDR
  always_comb begin
    if (sec_wipe_wdr_q) begin
      // Wipe the WDR with either random numbers or zeroes.
      if (sec_wipe_wdr_urnd_q) begin
        rf_bignum_wr_data_no_intg = urnd_data;
      end else begin
        rf_bignum_wr_data_no_intg = 256'b0;
      end
      rf_bignum_wr_data_intg_sel = 0;
    end else begin
      rf_bignum_wr_data_no_intg = rf_bignum_wr_data_no_intg_ctrl;
      rf_bignum_wr_data_intg_sel = rf_bignum_wr_data_intg_sel_ctrl;
    end
  end

  otbn_alu_bignum u_otbn_alu_bignum (
    .clk_i,
    .rst_ni,

    .operation_i       (alu_bignum_operation),
    .operation_valid_i (alu_bignum_operation_valid),
    .operation_commit_i(alu_bignum_operation_commit),
    .operation_result_o(alu_bignum_operation_result),
    .selection_flag_o  (alu_bignum_selection_flag),

    .alu_predec_bignum_i (alu_predec_bignum),
    .ispr_predec_bignum_i(ispr_predec_bignum),

    .ispr_addr_i             (ispr_addr),
    .ispr_base_wdata_i       (ispr_base_wdata),
    .ispr_base_wr_en_i       (ispr_base_wr_en),
    .ispr_bignum_wdata_intg_i(ispr_bignum_wdata_intg),
    .ispr_bignum_wr_en_i     (ispr_bignum_wr_en),
    .ispr_wr_commit_i        (ispr_wr_commit),
    .ispr_init_i             (ispr_init),
    .ispr_rdata_intg_o       (ispr_rdata_intg),
    .ispr_rd_en_i            (ispr_rd_en),

    .ispr_acc_intg_i        (ispr_acc_intg),
    .ispr_acc_wr_data_intg_o(ispr_acc_wr_data_intg),
    .ispr_acc_wr_en_o       (ispr_acc_wr_en),

    .reg_intg_violation_err_o(alu_bignum_reg_intg_violation_err),

    .sec_wipe_mod_urnd_i(sec_wipe_mod_urnd),
    .sec_wipe_zero_i    (sec_wipe_zero),

    .mac_operation_flags_i   (mac_bignum_operation_flags),
    .mac_operation_flags_en_i(mac_bignum_operation_flags_en),

    .rnd_data_i (rnd_data),
    .urnd_data_i(urnd_data),

    .sideload_key_shares_i,

    .alu_predec_error_o(alu_bignum_predec_error),
    .ispr_predec_error_o(ispr_predec_error)
  );

  otbn_mac_bignum u_otbn_mac_bignum (
    .clk_i,
    .rst_ni,

    .operation_i                    (mac_bignum_operation),
    .operation_result_o             (mac_bignum_operation_result),
    .operation_flags_o              (mac_bignum_operation_flags),
    .operation_flags_en_o           (mac_bignum_operation_flags_en),
    .operation_intg_violation_err_o (mac_bignum_reg_intg_violation_err),

    .mac_predec_bignum_i(mac_predec_bignum),
    .predec_error_o     (mac_bignum_predec_error),

    .urnd_data_i        (urnd_data),
    .sec_wipe_acc_urnd_i(sec_wipe_acc_urnd),

    .mac_en_i    (mac_bignum_en),
    .mac_commit_i(mac_bignum_commit),

    .ispr_acc_intg_o        (ispr_acc_intg),
    .ispr_acc_wr_data_intg_i(ispr_acc_wr_data_intg),
    .ispr_acc_wr_en_i       (ispr_acc_wr_en)
  );

  otbn_rnd #(
    .RndCnstUrndPrngSeed(RndCnstUrndPrngSeed)
  ) u_otbn_rnd (
    .clk_i,
    .rst_ni,

    .opn_start_i (controller_start),
    .opn_end_i   (secure_wipe_req),

    .rnd_req_i         (rnd_req),
    .rnd_prefetch_req_i(rnd_prefetch_req),
    .rnd_valid_o       (rnd_valid),
    .rnd_data_o        (rnd_data),
    .rnd_rep_err_o     (rnd_rep_err),
    .rnd_fips_err_o    (rnd_fips_err),

    .urnd_reseed_req_i (urnd_reseed_req),
    .urnd_reseed_ack_o (urnd_reseed_ack),
    .urnd_advance_i    (urnd_advance),
    .urnd_data_o       (urnd_data),
    .urnd_all_zero_o   (urnd_all_zero),

    .edn_rnd_req_o,
    .edn_rnd_ack_i,
    .edn_rnd_data_i,
    .edn_rnd_fips_i,
    .edn_rnd_err_i,

    .edn_urnd_req_o,
    .edn_urnd_ack_i,
    .edn_urnd_data_i
  );

  // Advance URND either when the start_stop_control commands it or when temporary secure wipe keys
  // are requested.
  // When SecMuteUrnd is enabled, signal urnd_advance_start_stop_control is muted. Therefore, it is
  // necessary to enable urnd_advance using ispr_predec_bignum.ispr_rd_en[IsprUrnd] whenever URND
  // data are consumed by the ALU.
  assign urnd_advance = urnd_advance_start_stop_control | req_sec_wipe_urnd_keys_q |
                        (SecMuteUrnd & ispr_predec_bignum.ispr_rd_en[IsprUrnd]);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_sec_wipe_urnd_keys_q <= 1'b0;
    end else begin
      req_sec_wipe_urnd_keys_q <= req_sec_wipe_urnd_keys_i;
    end
  end

  assign dmem_sec_wipe_urnd_key_o = urnd_data[127:0];
  assign imem_sec_wipe_urnd_key_o = urnd_data[255:128];

  // Asserts =======================================================================================

  // All outputs should be known.
  `ASSERT_KNOWN(DoneOKnown_A, done_o)
  `ASSERT_KNOWN(ImemReqOKnown_A, imem_req_o)
  `ASSERT_KNOWN_IF(ImemAddrOKnown_A, imem_addr_o, imem_req_o)
  `ASSERT_KNOWN(DmemReqOKnown_A, dmem_req_o)
  `ASSERT_KNOWN_IF(DmemWriteOKnown_A, dmem_write_o, dmem_req_o)
  `ASSERT_KNOWN_IF(DmemAddrOKnown_A, dmem_addr_o, dmem_req_o)
  `ASSERT_KNOWN_IF(DmemWdataOKnown_A, dmem_wdata_o, dmem_req_o & dmem_write_o)
  `ASSERT_KNOWN_IF(DmemWmaskOKnown_A, dmem_wmask_o, dmem_req_o & dmem_write_o)
  `ASSERT_KNOWN_IF(DmemRmaskOKnown_A, dmem_rmask_o, dmem_req_o)
  `ASSERT_KNOWN(EdnRndReqOKnown_A, edn_rnd_req_o)
  `ASSERT_KNOWN(EdnUrndReqOKnown_A, edn_urnd_req_o)
  `ASSERT_KNOWN(InsnCntOKnown_A, insn_cnt_o)
  `ASSERT_KNOWN(ErrBitsKnown_A, err_bits_o)

  // Keep the EDN requests active until they are acknowledged.
  `ASSERT(EdnRndReqStable_A, edn_rnd_req_o & ~edn_rnd_ack_i |=> edn_rnd_req_o)
  `ASSERT(EdnUrndReqStable_A, edn_urnd_req_o & ~edn_urnd_ack_i |=> edn_urnd_req_o)

  `ASSERT(OnlyWriteLoadDataBaseWhenDMemValid_A,
          rf_bignum_wr_en_ctrl & insn_dec_bignum.rf_wdata_sel == RfWdSelLsu |-> dmem_rvalid_i)
  `ASSERT(OnlyWriteLoadDataBignumWhenDMemValid_A,
          rf_base_wr_en_ctrl & insn_dec_base.rf_wdata_sel == RfWdSelLsu |-> dmem_rvalid_i)

  // Error handling: if we pass an error signal down to the controller then we should also be
  // setting an error flag, unless the signal came from above.
  `ASSERT(ErrBitsIfControllerEscalate_A,
          (mubi4_test_true_loose(controller_fatal_escalate_en) ||
           mubi4_test_true_loose(controller_recov_escalate_en)) &&
          mubi4_test_false_strict(escalate_en_i)
          |=> err_bits_q)

  // Similarly, if we pass an escalation signal down to the start/stop controller then we should
  // also be setting an error flag, unless the signal came from above.
  `ASSERT(ErrBitsIfStartStopEscalate_A,
          mubi4_test_true_loose(start_stop_escalate_en) && mubi4_test_false_strict(escalate_en_i)
          |=> err_bits_q)

  // The following assertions allow up to 400 cycles from escalation until the start/stop FSM locks.
  // This is a long time, but it's necessary because following an escalation the start/stop FSM goes
  // through two rounds of secure wiping with random data with an URND reseed in between.  Depending
  // on the delay configured in the EDN model, the reseed alone can take 200 cycles.

  `ASSERT(OtbnStartStopGlobalEscCntrMeasure_A, err_bits_q && mubi4_test_true_loose(escalate_en_i)
          && mubi4_test_true_loose(start_stop_escalate_en)|=> ##[1:400]
          u_otbn_start_stop_control.state_q == otbn_pkg::OtbnStartStopStateLocked)

  `ASSERT(OtbnStartStopLocalEscCntrMeasure_A, err_bits_q && mubi4_test_false_strict(escalate_en_i)
          && mubi4_test_true_loose(start_stop_escalate_en) |=>  ##[1:400]
          u_otbn_start_stop_control.state_q == otbn_pkg::OtbnStartStopStateLocked)

  // In contrast to the start/stop FSM, the controller FSM should lock quickly after an escalation,
  // independent of the secure wipe.

  `ASSERT(OtbnControllerGlobalEscCntrMeasure_A, err_bits_q && mubi4_test_true_loose(escalate_en_i)
          && mubi4_test_true_loose(controller_fatal_escalate_en)|=> ##[1:100]
          u_otbn_controller.state_q == otbn_pkg::OtbnStateLocked)

  `ASSERT(OtbnControllerLocalEscCntrMeasure_A, err_bits_q && mubi4_test_false_strict(escalate_en_i)
          && mubi4_test_true_loose(controller_fatal_escalate_en) |=>  ##[1:100]
          u_otbn_controller.state_q == otbn_pkg::OtbnStateLocked)

endmodule
