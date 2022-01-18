// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OpenTitan Big Number Accelerator (OTBN) Core
 *
 * This module is the top-level of the OTBN processing core.
 */
module otbn_core
  import otbn_pkg::*;
#(
  // Register file implementation selection, see otbn_pkg.sv.
  parameter regfile_e RegFile = RegFileFF,

  // Size of the instruction memory, in bytes
  parameter int ImemSizeByte = 4096,
  // Size of the data memory, in bytes
  parameter int DmemSizeByte = 4096,
  // Enable internal secure wipe
  parameter bit SecWipeEn = 1'b0,

  // Default seed for URND PRNG
  parameter urnd_prng_seed_t RndCnstUrndPrngSeed = RndCnstUrndPrngSeedDefault,

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte),
  localparam int DmemAddrWidth = prim_util_pkg::vbits(DmemSizeByte)
) (
  input logic clk_i,
  input logic rst_ni,

  input  logic start_i,  // start the operation
  output logic done_o,   // operation done
  output logic locked_o, // otbn locked, reset required to perform further commands

  output err_bits_t err_bits_o,  // valid when done_o is asserted
  output logic recoverable_err_o,
  output logic reg_intg_violation_o,

  // Instruction memory (IMEM)
  output logic                     imem_req_o,
  output logic [ImemAddrWidth-1:0] imem_addr_o,
  input  logic [38:0]              imem_rdata_i,
  input  logic                     imem_rvalid_i,

  output logic insn_fetch_err_o,

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

  output logic                    edn_urnd_req_o,
  input  logic                    edn_urnd_ack_i,
  input  logic [EdnDataWidth-1:0] edn_urnd_data_i,

  output logic [31:0] insn_cnt_o,
  input  logic        insn_cnt_clear_i,

  // An integrity check on an incoming bus transaction failed. Results in a fatal error.
  input logic bus_intg_violation_i,

  // Asserted by system when bus tries to access OTBN memories whilst OTBN is active. Results in a
  // fatal error.
  input logic illegal_bus_access_i,

  // Indicates an incoming escalation from the life cycle manager. Results in a fatal error.
  input logic lifecycle_escalation_i,

  // When set software errors become fatal errors.
  input logic software_errs_fatal_i,

  // Indicates an invalid state of the scramble controller. Results in a fatal error.
  input logic otbn_scramble_state_error_i,

  input logic [1:0]                       sideload_key_shares_valid_i,
  input logic [1:0][SideloadKeyWidth-1:0] sideload_key_shares_i
);
  // Fetch request (the next instruction)
  logic [ImemAddrWidth-1:0] insn_fetch_req_addr;
  logic                     insn_fetch_req_valid;

  // Fetch response (the current instruction before it is decoded)
  logic                     insn_fetch_resp_valid;
  logic [ImemAddrWidth-1:0] insn_fetch_resp_addr;
  logic [31:0]              insn_fetch_resp_data;
  logic                     insn_fetch_resp_clear;
  logic                     insn_fetch_err;

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
  logic                     rf_base_wr_data_intg_sel;
  logic [4:0]               rf_base_rd_addr_a;
  logic                     rf_base_rd_en_a;
  logic [BaseIntgWidth-1:0] rf_base_rd_data_a_intg;
  logic [4:0]               rf_base_rd_addr_b;
  logic                     rf_base_rd_en_b;
  logic [BaseIntgWidth-1:0] rf_base_rd_data_b_intg;
  logic                     rf_base_rd_commit;
  logic                     rf_base_call_stack_err;
  logic                     rf_base_rd_data_err;

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
  logic [WLEN-1:0]    rf_bignum_wr_data_no_intg;
  logic [WLEN-1:0]    rf_bignum_wr_data_no_intg_ctrl;
  logic [ExtWLEN-1:0] rf_bignum_wr_data_intg;
  logic               rf_bignum_wr_data_intg_sel;
  logic [WdrAw-1:0]   rf_bignum_rd_addr_a;
  logic               rf_bignum_rd_en_a;
  logic [ExtWLEN-1:0] rf_bignum_rd_data_a_intg;
  logic [WdrAw-1:0]   rf_bignum_rd_addr_b;
  logic               rf_bignum_rd_en_b;
  logic [ExtWLEN-1:0] rf_bignum_rd_data_b_intg;
  logic               rf_bignum_rd_data_err;

  alu_bignum_operation_t alu_bignum_operation;
  logic [WLEN-1:0]       alu_bignum_operation_result;
  logic                  alu_bignum_selection_flag;

  mac_bignum_operation_t mac_bignum_operation;
  logic [WLEN-1:0]       mac_bignum_operation_result;
  flags_t                mac_bignum_operation_flags;
  flags_t                mac_bignum_operation_flags_en;
  logic                  mac_bignum_en;

  ispr_e                       ispr_addr;
  logic [31:0]                 ispr_base_wdata;
  logic [BaseWordsPerWLEN-1:0] ispr_base_wr_en;
  logic [WLEN-1:0]             ispr_bignum_wdata;
  logic                        ispr_bignum_wr_en;
  logic [WLEN-1:0]             ispr_rdata;
  logic [WLEN-1:0]             ispr_acc;
  logic [WLEN-1:0]             ispr_acc_wr_data;
  logic                        ispr_acc_wr_en;
  logic                        ispr_init;

  logic            rnd_req;
  logic            rnd_prefetch_req;
  logic            rnd_valid;
  logic [WLEN-1:0] rnd_data;

  logic            urnd_reseed_req;
  logic            urnd_reseed_busy;
  logic            urnd_advance;
  logic [WLEN-1:0] urnd_data;
  logic            urnd_all_zero;

  logic        controller_start;

  logic        state_reset;
  logic [31:0] insn_cnt;

  logic start_secure_wipe;
  logic secure_wipe_running;

  logic sec_wipe_wdr;
  logic sec_wipe_wdr_urnd;
  logic sec_wipe_base;
  logic sec_wipe_base_urnd;
  logic [4:0] sec_wipe_addr;

  logic sec_wipe_acc_urnd;
  logic sec_wipe_mod_urnd;
  logic sec_wipe_zero;

  logic                     prefetch_en;
  logic                     prefetch_loop_active;
  logic [31:0]              prefetch_loop_iterations;
  logic [ImemAddrWidth:0]   prefetch_loop_end_addr;
  logic [ImemAddrWidth-1:0] prefetch_loop_jump_addr;

  logic start_stop_state_error;

  // Start stop control start OTBN execution when requested and deals with any pre start or post
  // stop actions.
  otbn_start_stop_control #(
    .SecWipeEn(SecWipeEn)
  ) u_otbn_start_stop_control (
    .clk_i,
    .rst_ni,

    .start_i,

    .controller_start_o(controller_start),

    .urnd_reseed_req_o (urnd_reseed_req),
    .urnd_reseed_busy_i(urnd_reseed_busy),
    .urnd_advance_o    (urnd_advance),

    .start_secure_wipe_i  (start_secure_wipe),
    .secure_wipe_running_o(secure_wipe_running),
    .done_o,

    .sec_wipe_wdr_o      (sec_wipe_wdr),
    .sec_wipe_wdr_urnd_o (sec_wipe_wdr_urnd),
    .sec_wipe_base_o     (sec_wipe_base),
    .sec_wipe_base_urnd_o(sec_wipe_base_urnd),
    .sec_wipe_addr_o     (sec_wipe_addr),

    .sec_wipe_acc_urnd_o(sec_wipe_acc_urnd),
    .sec_wipe_mod_urnd_o(sec_wipe_mod_urnd),
    .sec_wipe_zero_o    (sec_wipe_zero),

    .ispr_init_o  (ispr_init),
    .state_reset_o(state_reset),
    .state_error_o(start_stop_state_error)
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
    .insn_fetch_req_addr_i (insn_fetch_req_addr),
    .insn_fetch_req_valid_i(insn_fetch_req_valid),

    // Fetched instruction
    .insn_fetch_resp_addr_o (insn_fetch_resp_addr),
    .insn_fetch_resp_valid_o(insn_fetch_resp_valid),
    .insn_fetch_resp_data_o (insn_fetch_resp_data),
    .insn_fetch_resp_clear_i(insn_fetch_resp_clear),
    .insn_fetch_err_o       (insn_fetch_err),

    .prefetch_en_i             (prefetch_en),
    .prefetch_loop_active_i    (prefetch_loop_active),
    .prefetch_loop_iterations_i(prefetch_loop_iterations),
    .prefetch_loop_end_addr_i  (prefetch_loop_end_addr),
    .prefetch_loop_jump_addr_i (prefetch_loop_jump_addr)
  );

  assign insn_fetch_err_o = insn_fetch_err;

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

  // Controller: coordinate between functional units, prepare their inputs (e.g. by muxing between
  // operand sources), and post-process their outputs as needed.
  otbn_controller #(
    .ImemSizeByte(ImemSizeByte),
    .DmemSizeByte(DmemSizeByte),
    .SecWipeEn(SecWipeEn)
  ) u_otbn_controller (
    .clk_i,
    .rst_ni,

    .start_i(controller_start),
    .locked_o,

    .err_bits_o,
    .recoverable_err_o,
    .reg_intg_violation_o,

    // Next instruction selection (to instruction fetch)
    .insn_fetch_req_addr_o  (insn_fetch_req_addr),
    .insn_fetch_req_valid_o (insn_fetch_req_valid),
    .insn_fetch_resp_clear_o(insn_fetch_resp_clear),
    // Error from fetch requested last cycle
    .insn_fetch_err_i       (insn_fetch_err),

    // The current instruction
    .insn_valid_i  (insn_valid),
    .insn_illegal_i(insn_illegal),
    .insn_addr_i   (insn_addr),

    // Decoded instruction from decoder
    .insn_dec_base_i  (insn_dec_base),
    .insn_dec_bignum_i(insn_dec_bignum),
    .insn_dec_shared_i(insn_dec_shared),

    // To/from base register file
    .rf_base_wr_addr_o         (rf_base_wr_addr_ctrl),
    .rf_base_wr_en_o           (rf_base_wr_en_ctrl),
    .rf_base_wr_commit_o       (rf_base_wr_commit_ctrl),
    .rf_base_wr_data_no_intg_o (rf_base_wr_data_no_intg_ctrl),
    .rf_base_wr_data_intg_o    (rf_base_wr_data_intg),
    .rf_base_wr_data_intg_sel_o(rf_base_wr_data_intg_sel),
    .rf_base_rd_addr_a_o       (rf_base_rd_addr_a),
    .rf_base_rd_en_a_o         (rf_base_rd_en_a),
    .rf_base_rd_data_a_intg_i  (rf_base_rd_data_a_intg),
    .rf_base_rd_addr_b_o       (rf_base_rd_addr_b),
    .rf_base_rd_en_b_o         (rf_base_rd_en_b),
    .rf_base_rd_data_b_intg_i  (rf_base_rd_data_b_intg),
    .rf_base_rd_commit_o       (rf_base_rd_commit),
    .rf_base_call_stack_err_i  (rf_base_call_stack_err),
    .rf_base_rd_data_err_i     (rf_base_rd_data_err),

    // To/from bignunm register file
    .rf_bignum_wr_addr_o         (rf_bignum_wr_addr_ctrl),
    .rf_bignum_wr_en_o           (rf_bignum_wr_en_ctrl),
    .rf_bignum_wr_data_no_intg_o (rf_bignum_wr_data_no_intg_ctrl),
    .rf_bignum_wr_data_intg_o    (rf_bignum_wr_data_intg),
    .rf_bignum_wr_data_intg_sel_o(rf_bignum_wr_data_intg_sel),
    .rf_bignum_rd_addr_a_o       (rf_bignum_rd_addr_a),
    .rf_bignum_rd_en_a_o         (rf_bignum_rd_en_a),
    .rf_bignum_rd_data_a_intg_i  (rf_bignum_rd_data_a_intg),
    .rf_bignum_rd_addr_b_o       (rf_bignum_rd_addr_b),
    .rf_bignum_rd_en_b_o         (rf_bignum_rd_en_b),
    .rf_bignum_rd_data_b_intg_i  (rf_bignum_rd_data_b_intg),
    .rf_bignum_rd_data_err_i     (rf_bignum_rd_data_err),

    // To/from base ALU
    .alu_base_operation_o        (alu_base_operation),
    .alu_base_comparison_o       (alu_base_comparison),
    .alu_base_operation_result_i (alu_base_operation_result),
    .alu_base_comparison_result_i(alu_base_comparison_result),

    // To/from bignum ALU
    .alu_bignum_operation_o       (alu_bignum_operation),
    .alu_bignum_operation_result_i(alu_bignum_operation_result),
    .alu_bignum_selection_flag_i  (alu_bignum_selection_flag),

    // To/from bignum MAC
    .mac_bignum_operation_o       (mac_bignum_operation),
    .mac_bignum_operation_result_i(mac_bignum_operation_result),
    .mac_bignum_en_o              (mac_bignum_en),

    // To/from LSU (base and bignum)
    .lsu_load_req_o  (lsu_load_req),
    .lsu_store_req_o (lsu_store_req),
    .lsu_req_subset_o(lsu_req_subset),
    .lsu_addr_o      (lsu_addr),

    .lsu_base_wdata_o  (lsu_base_wdata),
    .lsu_bignum_wdata_o(lsu_bignum_wdata),

    .lsu_base_rdata_i  (lsu_base_rdata),
    .lsu_bignum_rdata_i(lsu_bignum_rdata),
    .lsu_rdata_err_i   (lsu_rdata_err),

    // Isprs read/write (base and bignum)
    .ispr_addr_o        (ispr_addr),
    .ispr_base_wdata_o  (ispr_base_wdata),
    .ispr_base_wr_en_o  (ispr_base_wr_en),
    .ispr_bignum_wdata_o(ispr_bignum_wdata),
    .ispr_bignum_wr_en_o(ispr_bignum_wr_en),
    .ispr_rdata_i       (ispr_rdata),

    .rnd_req_o         (rnd_req),
    .rnd_prefetch_req_o(rnd_prefetch_req),
    .rnd_valid_i       (rnd_valid),
    .urnd_state_err_i  (urnd_all_zero),

    // Secure wipe
    .secure_wipe_running_i(secure_wipe_running),
    .start_secure_wipe_o  (start_secure_wipe),
    .sec_wipe_zero_i      (sec_wipe_zero),

    .state_reset_i(state_reset),
    .insn_cnt_o   (insn_cnt),
    .insn_cnt_clear_i,
    .bus_intg_violation_i,
    .illegal_bus_access_i,
    .lifecycle_escalation_i,
    .software_errs_fatal_i,
    .start_stop_state_error_i(start_stop_state_error),
    .otbn_scramble_state_error_i,

    .sideload_key_shares_valid_i,

    .prefetch_en_o             (prefetch_en),
    .prefetch_loop_active_o    (prefetch_loop_active),
    .prefetch_loop_iterations_o(prefetch_loop_iterations),
    .prefetch_loop_end_addr_o  (prefetch_loop_end_addr),
    .prefetch_loop_jump_addr_o (prefetch_loop_jump_addr)
  );

  `ASSERT(InsnDataStableInStall, u_otbn_controller.state_q == OtbnStateStall |->
                                 insn_fetch_resp_data == $past(insn_fetch_resp_data))

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

    .call_stack_err_o(rf_base_call_stack_err),
    .rd_data_err_o   (rf_base_rd_data_err)
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
    end else begin
      rf_base_wr_data_no_intg = rf_base_wr_data_no_intg_ctrl;
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
    .wr_data_no_intg_i (rf_bignum_wr_data_no_intg),
    .wr_data_intg_i    (rf_bignum_wr_data_intg),
    .wr_data_intg_sel_i(rf_bignum_wr_data_intg_sel),

    .rd_addr_a_i     (rf_bignum_rd_addr_a),
    .rd_en_a_i       (rf_bignum_rd_en_a),
    .rd_data_a_intg_o(rf_bignum_rd_data_a_intg),
    .rd_addr_b_i     (rf_bignum_rd_addr_b),
    .rd_en_b_i       (rf_bignum_rd_en_b),
    .rd_data_b_intg_o(rf_bignum_rd_data_b_intg),

    .rd_data_err_o(rf_bignum_rd_data_err)
  );

  assign rf_bignum_wr_addr         = sec_wipe_wdr ? sec_wipe_addr : rf_bignum_wr_addr_ctrl;
  assign rf_bignum_wr_en           = sec_wipe_wdr ? 2'b11         : rf_bignum_wr_en_ctrl;

  // Write data to WDR
  always_comb begin
    if (sec_wipe_wdr) begin
      // Wipe the WDR with either random numbers or zeroes.
      if (sec_wipe_wdr_urnd) begin
        rf_bignum_wr_data_no_intg = urnd_data;
      end else begin
        rf_bignum_wr_data_no_intg = 256'b0;
      end
    end else begin
      rf_bignum_wr_data_no_intg = rf_bignum_wr_data_no_intg_ctrl;
    end
  end

  otbn_alu_bignum u_otbn_alu_bignum (
    .clk_i,
    .rst_ni,

    .operation_i       (alu_bignum_operation),
    .operation_result_o(alu_bignum_operation_result),
    .selection_flag_o  (alu_bignum_selection_flag),

    .ispr_addr_i        (ispr_addr),
    .ispr_base_wdata_i  (ispr_base_wdata),
    .ispr_base_wr_en_i  (ispr_base_wr_en),
    .ispr_bignum_wdata_i(ispr_bignum_wdata),
    .ispr_bignum_wr_en_i(ispr_bignum_wr_en),
    .ispr_init_i        (ispr_init),
    .ispr_rdata_o       (ispr_rdata),

    .ispr_acc_i        (ispr_acc),
    .ispr_acc_wr_data_o(ispr_acc_wr_data),
    .ispr_acc_wr_en_o  (ispr_acc_wr_en),

    .sec_wipe_mod_urnd_i(sec_wipe_mod_urnd),
    .sec_wipe_zero_i    (sec_wipe_zero),

    .mac_operation_flags_i   (mac_bignum_operation_flags),
    .mac_operation_flags_en_i(mac_bignum_operation_flags_en),

    .rnd_data_i (rnd_data),
    .urnd_data_i(urnd_data),

    .sideload_key_shares_i
  );

  otbn_mac_bignum u_otbn_mac_bignum (
    .clk_i,
    .rst_ni,

    .operation_i         (mac_bignum_operation),
    .operation_result_o  (mac_bignum_operation_result),
    .operation_flags_o   (mac_bignum_operation_flags),
    .operation_flags_en_o(mac_bignum_operation_flags_en),

    .urnd_data_i        (urnd_data),
    .sec_wipe_acc_urnd_i(sec_wipe_acc_urnd),
    .sec_wipe_zero_i    (sec_wipe_zero),

    .mac_en_i(mac_bignum_en),

    .ispr_acc_o        (ispr_acc),
    .ispr_acc_wr_data_i(ispr_acc_wr_data),
    .ispr_acc_wr_en_i  (ispr_acc_wr_en)
  );

  otbn_rnd #(
    .RndCnstUrndPrngSeed(RndCnstUrndPrngSeed)
  ) u_otbn_rnd (
    .clk_i,
    .rst_ni,

    .rnd_req_i         (rnd_req),
    .rnd_prefetch_req_i(rnd_prefetch_req),
    .rnd_valid_o       (rnd_valid),
    .rnd_data_o        (rnd_data),

    .urnd_reseed_req_i (urnd_reseed_req),
    .urnd_reseed_busy_o(urnd_reseed_busy),
    .urnd_advance_i    (urnd_advance),
    .urnd_data_o       (urnd_data),
    .urnd_all_zero_o   (urnd_all_zero),

    .edn_rnd_req_o,
    .edn_rnd_ack_i,
    .edn_rnd_data_i,

    .edn_urnd_req_o,
    .edn_urnd_ack_i,
    .edn_urnd_data_i
  );

  // Asserts =======================================================================================

  // All outputs should be known.
  `ASSERT_KNOWN(DoneOKnown_A, done_o)
  `ASSERT_KNOWN(ImemReqOKnown_A, imem_req_o)
  `ASSERT_KNOWN_IF(ImemAddrOKnown_A, imem_addr_o, imem_req_o)
  `ASSERT_KNOWN(DmemReqOKnown_A, dmem_req_o)
  `ASSERT_KNOWN_IF(DmemWriteOKnown_A, dmem_write_o, dmem_req_o)
  `ASSERT_KNOWN_IF(DmemAddrOKnown_A, dmem_addr_o, dmem_req_o)
  `ASSERT_KNOWN_IF(DmemWdataOKnown_A, dmem_wdata_o, dmem_req_o)
  `ASSERT_KNOWN_IF(DmemRmaskOKnown_A, dmem_rmask_o, dmem_req_o)
  `ASSERT_KNOWN(EdnRndReqOKnown_A, edn_rnd_req_o)
  `ASSERT_KNOWN(EdnUrndReqOKnown_A, edn_urnd_req_o)
  `ASSERT_KNOWN(InsnCntOKnown_A, insn_cnt_o)

  // Keep the EDN requests active until they are acknowledged.
  `ASSERT(EdnRndReqStable_A, edn_rnd_req_o & ~edn_rnd_ack_i |=> edn_rnd_req_o)
  `ASSERT(EdnUrndReqStable_A, edn_urnd_req_o & ~edn_urnd_ack_i |=> edn_urnd_req_o)

  `ASSERT(OnlyWriteLoadDataBaseWhenDMemValid_A,
          rf_bignum_wr_en_ctrl & insn_dec_bignum.rf_wdata_sel == RfWdSelLsu |-> dmem_rvalid_i)
  `ASSERT(OnlyWriteLoadDataBignumWhenDMemValid_A,
          rf_base_wr_en_ctrl & insn_dec_base.rf_wdata_sel == RfWdSelLsu |-> dmem_rvalid_i)
endmodule
