// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN Controller
 */
module otbn_controller
  import otbn_pkg::*;
#(
  // Size of the instruction memory, in bytes
  parameter int ImemSizeByte = 4096,
  // Size of the data memory, in bytes
  parameter int DmemSizeByte = 4096,

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte),
  localparam int DmemAddrWidth = prim_util_pkg::vbits(DmemSizeByte)
) (
  input logic clk_i,
  input logic rst_ni,

  input  logic start_i,   // start the processing at address zero
  output logic locking_o, // Controller is in or is entering the locked state
  input  logic err_bit_clear_i,

  input prim_mubi_pkg::mubi4_t fatal_escalate_en_i,
  input prim_mubi_pkg::mubi4_t recov_escalate_en_i,
  input prim_mubi_pkg::mubi4_t rma_req_i,
  output controller_err_bits_t err_bits_o,
  output logic                 recoverable_err_o,

  // Next instruction selection (to instruction fetch)
  output logic                     insn_fetch_req_valid_o,
  output logic                     insn_fetch_req_valid_raw_o,
  output logic [ImemAddrWidth-1:0] insn_fetch_req_addr_o,
  output logic                     insn_fetch_resp_clear_o,

  // Fetched/decoded instruction
  input logic                     insn_valid_i,
  input logic                     insn_illegal_i,
  input logic [ImemAddrWidth-1:0] insn_addr_i,

  // Decoded instruction data
  input insn_dec_base_t   insn_dec_base_i,
  input insn_dec_bignum_t insn_dec_bignum_i,
  input insn_dec_shared_t insn_dec_shared_i,

  // Base register file
  output logic [4:0]               rf_base_wr_addr_o,
  output logic                     rf_base_wr_en_o,
  output logic                     rf_base_wr_commit_o,
  output logic [31:0]              rf_base_wr_data_no_intg_o,
  output logic [BaseIntgWidth-1:0] rf_base_wr_data_intg_o,
  output logic                     rf_base_wr_data_intg_sel_o,

  output logic [4:0]               rf_base_rd_addr_a_o,
  output logic                     rf_base_rd_en_a_o,
  input  logic [BaseIntgWidth-1:0] rf_base_rd_data_a_intg_i,
  output logic [4:0]               rf_base_rd_addr_b_o,
  output logic                     rf_base_rd_en_b_o,
  input  logic [BaseIntgWidth-1:0] rf_base_rd_data_b_intg_i,
  output logic                     rf_base_rd_commit_o,

  input logic rf_base_call_stack_sw_err_i,
  input logic rf_base_call_stack_hw_err_i,

  // Bignum register file (WDRs)
  output logic [4:0]         rf_bignum_wr_addr_o,
  output logic [1:0]         rf_bignum_wr_en_o,
  output logic               rf_bignum_wr_commit_o,
  output logic [WLEN-1:0]    rf_bignum_wr_data_no_intg_o,
  output logic [ExtWLEN-1:0] rf_bignum_wr_data_intg_o,
  output logic               rf_bignum_wr_data_intg_sel_o,

  output logic [4:0]         rf_bignum_rd_addr_a_o,
  output logic               rf_bignum_rd_en_a_o,
  input  logic [ExtWLEN-1:0] rf_bignum_rd_data_a_intg_i,

  output logic [4:0]         rf_bignum_rd_addr_b_o,
  output logic               rf_bignum_rd_en_b_o,
  input  logic [ExtWLEN-1:0] rf_bignum_rd_data_b_intg_i,

  input logic rf_bignum_intg_err_i,
  input logic rf_bignum_spurious_we_err_i,

  output logic [NWdr-1:0] rf_bignum_rd_a_indirect_onehot_o,
  output logic [NWdr-1:0] rf_bignum_rd_b_indirect_onehot_o,
  output logic [NWdr-1:0] rf_bignum_wr_indirect_onehot_o,
  output logic            rf_bignum_indirect_en_o,

  // Execution units

  // Base ALU
  output alu_base_operation_t  alu_base_operation_o,
  output alu_base_comparison_t alu_base_comparison_o,
  input  logic [31:0]          alu_base_operation_result_i,
  input  logic                 alu_base_comparison_result_i,

  // Bignum ALU
  output alu_bignum_operation_t alu_bignum_operation_o,
  output logic                  alu_bignum_operation_valid_o,
  output logic                  alu_bignum_operation_commit_o,
  input  logic [WLEN-1:0]       alu_bignum_operation_result_i,
  input  logic                  alu_bignum_selection_flag_i,

  // Bignum MAC
  output mac_bignum_operation_t mac_bignum_operation_o,
  input  logic [WLEN-1:0]       mac_bignum_operation_result_i,
  output logic                  mac_bignum_en_o,
  output logic                  mac_bignum_commit_o,

  // LSU
  output logic                     lsu_load_req_o,
  output logic                     lsu_store_req_o,
  output insn_subset_e             lsu_req_subset_o,
  output logic [DmemAddrWidth-1:0] lsu_addr_o,
  input  logic                     lsu_addr_en_predec_i,

  output logic [BaseIntgWidth-1:0] lsu_base_wdata_o,
  output logic [ExtWLEN-1:0]       lsu_bignum_wdata_o,

  input  logic [BaseIntgWidth-1:0] lsu_base_rdata_i,
  input  logic [ExtWLEN-1:0]       lsu_bignum_rdata_i,

  // Internal Special-Purpose Registers (ISPRs)
  output ispr_e                       ispr_addr_o,
  output logic [31:0]                 ispr_base_wdata_o,
  output logic [BaseWordsPerWLEN-1:0] ispr_base_wr_en_o,
  output logic [ExtWLEN-1:0]          ispr_bignum_wdata_intg_o,
  output logic                        ispr_bignum_wr_en_o,
  output logic                        ispr_wr_commit_o,
  input  logic [ExtWLEN-1:0]          ispr_rdata_intg_i,
  output logic                        ispr_rd_en_o,

  // RND interface
  output logic rnd_req_o,
  output logic rnd_prefetch_req_o,
  input  logic rnd_valid_i,

  input  logic urnd_reseed_err_i,

  // Secure Wipe
  output logic secure_wipe_req_o,
  input  logic secure_wipe_ack_i,
  input  logic sec_wipe_zero_i,
  input  logic secure_wipe_running_i,

  input  logic        state_reset_i,
  output logic [31:0] insn_cnt_o,
  input  logic        insn_cnt_clear_i,
  output logic        mems_sec_wipe_o,

  input  logic        software_errs_fatal_i,

  input logic [1:0] sideload_key_shares_valid_i,

  // Prefetch stage control
  output logic                     prefetch_en_o,
  output logic                     prefetch_loop_active_o,
  output logic [31:0]              prefetch_loop_iterations_o,
  output logic [ImemAddrWidth:0]   prefetch_loop_end_addr_o,
  output logic [ImemAddrWidth-1:0] prefetch_loop_jump_addr_o,
  output logic                     prefetch_ignore_errs_o,

  // Predecoded control
  input  ctrl_flow_predec_t        ctrl_flow_predec_i,
  input  logic [ImemAddrWidth-1:0] ctrl_flow_target_predec_i,
  output logic                     predec_error_o
);
  import prim_mubi_pkg::*;

  otbn_state_e state_q, state_d;


  controller_err_bits_t err_bits_q, err_bits_d;

  // The specific error signals that go into err_bits_d
  logic fatal_software_err, bad_internal_state_err, reg_intg_violation_err, key_invalid_err;
  logic illegal_insn_err, bad_data_addr_err, call_stack_sw_err, bad_insn_addr_err;

  logic err;
  logic internal_err;
  logic recoverable_err;
  logic software_err;
  logic non_insn_addr_software_err;
  logic fatal_err;
  logic internal_fatal_err;
  logic done_complete;
  logic executing;
  logic state_error, state_error_d, state_error_q;
  logic spurious_secure_wipe_ack_q, spurious_secure_wipe_ack_d;
  logic mubi_err_q, mubi_err_d;

  logic                     insn_fetch_req_valid_raw;
  logic [ImemAddrWidth-1:0] insn_fetch_req_addr_last;

  logic stall;
  logic ispr_stall;
  logic mem_stall;
  logic rf_indirect_stall;
  logic jump_or_branch;
  logic branch_taken;
  logic insn_executing;
  logic ld_insn_with_addr_from_call_stack, st_insn_with_addr_from_call_stack;
  logic [ImemAddrWidth-1:0] branch_target;
  logic                     branch_target_overflow;
  logic [ImemAddrWidth:0]   next_insn_addr_wide;
  logic [ImemAddrWidth-1:0] next_insn_addr;

  csr_e                                csr_addr;
  logic [$clog2(BaseWordsPerWLEN)-1:0] csr_sub_addr;
  logic [31:0]                         csr_rdata_raw;
  logic [31:0]                         csr_rdata;
  logic [BaseWordsPerWLEN-1:0]         csr_rdata_mux [32];
  logic [31:0]                         csr_wdata_raw;
  logic [31:0]                         csr_wdata;

  wsr_e                                wsr_addr;
  logic [WLEN-1:0]                     wsr_wdata;

  ispr_e                               ispr_addr_base;
  logic [$clog2(BaseWordsPerWLEN)-1:0] ispr_word_addr_base;
  logic [BaseWordsPerWLEN-1:0]         ispr_word_sel_base;

  ispr_e                               ispr_addr_bignum;

  logic                                ispr_wr_insn, ispr_rd_insn;
  logic                                ispr_wr_base_insn;
  logic                                ispr_wr_bignum_insn;
  logic                                ispr_rd_bignum_insn;

  logic                     lsu_load_req_raw;
  logic                     lsu_store_req_raw;
  logic [DmemAddrWidth-1:0] lsu_addr, lsu_addr_blanked, lsu_addr_saved_d, lsu_addr_saved_q;
  logic                     lsu_addr_saved_sel;
  logic                     expected_lsu_addr_en;

  logic                     expected_call_stack_push, expected_call_stack_pop;
  logic                     lsu_predec_error, branch_target_predec_error, ctrl_predec_error;

  logic rnd_req_raw;

  // Register read data with integrity stripped off
  logic [31:0]     rf_base_rd_data_a_no_intg;
  logic [31:0]     rf_base_rd_data_b_no_intg;
  logic [WLEN-1:0] rf_bignum_rd_data_a_no_intg;
  logic [WLEN-1:0] rf_bignum_rd_data_b_no_intg;

  logic [ExtWLEN-1:0] selection_result;

  logic [1:0] rf_bignum_wr_en_unbuf;
  logic [4:0] rf_bignum_wr_addr_unbuf;
  logic [4:0] rf_bignum_rd_addr_a_unbuf;
  logic       rf_bignum_rd_en_a_unbuf;
  logic [4:0] rf_bignum_rd_addr_b_unbuf;
  logic       rf_bignum_rd_en_b_unbuf;

  logic rf_bignum_rd_a_indirect_en;
  logic rf_bignum_rd_b_indirect_en;
  logic rf_bignum_wr_indirect_en;

  // Computed increments for indirect register index and memory address in BN.LID/BN.SID/BN.MOVR
  // instructions.
  logic [5:0]  rf_base_rd_data_a_inc;
  logic [5:0]  rf_base_rd_data_b_inc;
  logic [26:0] rf_base_rd_data_a_wlen_word_inc;

  // Read/Write enables for base register file before illegal instruction encoding are factored in
  logic rf_base_rd_en_a_raw, rf_base_rd_en_b_raw, rf_base_wr_en_raw;

  // Output of mux taking the above increments as inputs and choosing one to write back to base
  // register file with appropriate zero extension and padding to give a 32-bit result.
  logic [31:0]              increment_out;

  // Loop control, used to start a new loop
  logic        loop_start_req;
  logic        loop_start_commit;
  logic        loop_reset;
  logic [11:0] loop_bodysize;
  logic [31:0] loop_iterations;

  // Loop generated jumps. The loop controller asks to jump when execution reaches the end of a loop
  // body that hasn't completed all of its iterations.
  logic                     loop_jump;
  logic [ImemAddrWidth-1:0] loop_jump_addr;

  logic [WLEN-1:0] mac_bignum_rf_wr_data;

  logic loop_hw_err, loop_predec_err;
  logic csr_illegal_addr, wsr_illegal_addr, ispr_illegal_addr;
  logic imem_addr_err, loop_sw_err, ispr_err;
  logic dmem_addr_err_check, dmem_addr_err;
  logic dmem_addr_unaligned_base, dmem_addr_unaligned_bignum, dmem_addr_overflow;
  logic illegal_insn_static;
  logic key_invalid;

  logic rf_a_indirect_err, rf_b_indirect_err, rf_d_indirect_err, rf_indirect_err;

  // If we are doing an indirect access to the bignum register file, it's possible that the
  // address that we use for the access is architecturally unknown. This happens if it came from x1
  // and we've underflowed the call stack. When this happens, we want to ignore any read data
  // integrity errors and spurious write enable errors since the access to the bignum register file
  // didn't happen architecturally anyway.
  logic ignore_rf_bignum_intg_errs;
  logic rf_bignum_intg_err;
  logic ignore_rf_bignum_spurious_we_errs;
  logic rf_bignum_spurious_we_err;

  logic ispr_rdata_intg_err;

  logic [31:0] insn_cnt_d, insn_cnt_q;
  logic        insn_cnt_clear;

  logic [4:0] insn_bignum_rd_addr_a_q, insn_bignum_rd_addr_b_q, insn_bignum_wr_addr_q;

  logic       start_secure_wipe;
  logic       secure_wipe_running_q, secure_wipe_running_d;

  assign secure_wipe_running_d = start_secure_wipe | (secure_wipe_running_q & ~secure_wipe_ack_i);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      secure_wipe_running_q <= 1'b0;
    end else begin
      secure_wipe_running_q <= secure_wipe_running_d;
    end
  end
  assign secure_wipe_req_o = start_secure_wipe | secure_wipe_running_q;

  // Spot spurious acks on the secure wipe interface. There is a an ack at the end of the initial
  // secure wipe, and as `secure_wipe_running_q` is only high during secure wipes triggered by this
  // controller, we have to ignore acks before the initial secure wipe is done.  Register this
  // signal to break a circular path (a secure wipe can be triggered by a stop, and a spurious
  // secure wipe ack can trigger a stop).
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      spurious_secure_wipe_ack_q <= 1'b0;
    end else begin
      spurious_secure_wipe_ack_q <= spurious_secure_wipe_ack_d;
    end
  end
  assign spurious_secure_wipe_ack_d = spurious_secure_wipe_ack_q |
                                      (secure_wipe_ack_i      &
                                       ~secure_wipe_running_q &
                                       ~secure_wipe_running_i);

  // Stall a cycle on loads to allow load data writeback to happen the following cycle. Stall not
  // required on stores as there is no response to deal with.
  assign mem_stall = lsu_load_req_raw;

  // Reads to RND must stall until data is available
  assign ispr_stall = rnd_req_raw & ~rnd_valid_i;

  assign rf_indirect_stall = insn_valid_i &
                             (state_q != OtbnStateStall) &
                             (insn_dec_shared_i.subset == InsnSubsetBignum) &
                             (insn_dec_bignum_i.rf_a_indirect |
                              insn_dec_bignum_i.rf_b_indirect |
                              insn_dec_bignum_i.rf_d_indirect);

  assign stall = mem_stall | ispr_stall | rf_indirect_stall;

  // OTBN is done when it was executing something (in state OtbnStateRun or OtbnStateStall)
  // and either it executes an ecall or an error occurs. A pulse on the done signal raises the
  // 'done' interrupt and also tells the top-level to update its ERR_BITS status
  // register. The calculation that ecall triggered done is factored out as `done_complete` to
  // avoid logic loops in the error handling logic.
  assign done_complete = (insn_valid_i & insn_dec_shared_i.ecall_insn);
  assign executing = (state_q == OtbnStateRun) ||
                     (state_q == OtbnStateStall);

  // Set the *locking* output when the next state is the *locked* state and no secure wipe is
  // running or there is a URND reseed error.  `locking_o` is thus set only after the secure wipe
  // has completed or if it cannot complete due to an URND reseed error (in which case
  // `secure_wipe_req_o` and `urnd_reseed_err_i` will remain high).  The condition for secure wipe
  // running involves `secure_wipe_running_i`, which is high for the initial secure wipe, and
  // `secure_wipe_req_o`, which is high for post-execution secure wipes.
  assign locking_o = (state_d == OtbnStateLocked) & (~(secure_wipe_running_i | secure_wipe_req_o) |
                                                     urnd_reseed_err_i | mubi_err_d);

  assign start_secure_wipe = executing & (done_complete | err);

  assign jump_or_branch = (insn_valid_i &
                           (insn_dec_shared_i.branch_insn | insn_dec_shared_i.jump_insn));

  // Branch taken when there is a valid branch instruction and comparison passes or a valid jump
  // instruction (which is always taken)
  assign branch_taken = insn_valid_i &
                        ((insn_dec_shared_i.branch_insn & alu_base_comparison_result_i) |
                         insn_dec_shared_i.jump_insn);
  // Branch target computed by base ALU (PC + imm)
  assign branch_target = alu_base_operation_result_i[ImemAddrWidth-1:0];
  assign branch_target_overflow = |alu_base_operation_result_i[31:ImemAddrWidth];

  assign next_insn_addr_wide = {1'b0, insn_addr_i} + 'd4;
  assign next_insn_addr = next_insn_addr_wide[ImemAddrWidth-1:0];

  // Record address for fetch request so it can be retried when an invalid response is received
  always_ff @(posedge clk_i) begin
    if (insn_fetch_req_valid_raw) begin
      insn_fetch_req_addr_last <= insn_fetch_req_addr_o;
    end
  end

  always_comb begin
    state_d                  = state_q;
    // `insn_fetch_req_valid_raw` is the value `insn_fetch_req_valid_o` before any errors are
    // considered.
    insn_fetch_req_valid_raw = 1'b0;
    insn_fetch_req_addr_o    = '0;
    insn_fetch_resp_clear_o  = 1'b1;
    prefetch_en_o            = 1'b0;

    state_error = 1'b0;

    unique case (state_q)
      OtbnStateHalt: begin
        if (start_i) begin
          state_d = OtbnStateRun;

          insn_fetch_req_addr_o    = '0;
          insn_fetch_req_valid_raw = 1'b1;
          prefetch_en_o            = 1'b1;
        end
      end
      OtbnStateRun: begin
        insn_fetch_req_valid_raw = 1'b1;
        prefetch_en_o            = 1'b1;

        if (!insn_valid_i) begin
          insn_fetch_req_addr_o = insn_fetch_req_addr_last;
        end else if (done_complete) begin
          state_d                  = OtbnStateHalt;
          insn_fetch_req_valid_raw = 1'b0;
          prefetch_en_o            = 1'b0;
        end else begin
          if (stall) begin
            // When stalling don't request a new fetch and don't clear response either to keep
            // current instruction.
            state_d                  = OtbnStateStall;
            insn_fetch_req_valid_raw = 1'b0;
            insn_fetch_resp_clear_o  = 1'b0;
          end else begin
            if (branch_taken) begin
              insn_fetch_req_addr_o = branch_target;
            end else if (loop_jump) begin
              insn_fetch_req_addr_o = loop_jump_addr;
            end else begin
              insn_fetch_req_addr_o = next_insn_addr;
            end
          end
        end
      end
      OtbnStateStall: begin
        prefetch_en_o = 1'b1;
        // When stalling refetch the same instruction to keep decode inputs constant
        if (stall) begin
          state_d                  = OtbnStateStall;
          //insn_fetch_req_addr_o = insn_addr_i;
          insn_fetch_req_valid_raw = 1'b0;
          insn_fetch_resp_clear_o  = 1'b0;
        end else begin
          insn_fetch_req_valid_raw = 1'b1;

          if (loop_jump) begin
            insn_fetch_req_addr_o = loop_jump_addr;
          end else begin
            insn_fetch_req_addr_o = next_insn_addr;
          end

          state_d = OtbnStateRun;
        end
      end
      OtbnStateLocked: begin
        insn_fetch_req_valid_raw = 1'b0;
        state_d                  = OtbnStateLocked;
      end
      default: begin
        // We should never get here. If we do (e.g. via a malicious glitch), error out immediately.
        // SEC_CM: CONTROLLER.FSM.LOCAL_ESC
        state_d = OtbnStateLocked;
        state_error = 1'b1;
      end
    endcase

    // On any error immediately halt, either going to OtbnStateLocked or OtbnStateHalt depending on
    // whether it was a fatal error.
    if (err) begin
      prefetch_en_o           = 1'b0;
      insn_fetch_resp_clear_o = 1'b1;

      if (fatal_err) begin
        // SEC_CM: CONTROLLER.FSM.GLOBAL_ESC
        state_d = OtbnStateLocked;
      end else begin
        state_d = OtbnStateHalt;
      end
    end

    // Regardless of what happens above enforce staying in OtnbStateLocked.
    if (state_q == OtbnStateLocked) begin
      state_d = OtbnStateLocked;
    end
  end

  assign state_error_d = state_error | state_error_q;

  prim_flop #(
    .Width(1),
    .ResetValue('0)
  ) u_state_error_flop (
    .clk_i,
    .rst_ni,

    .d_i(state_error_d),
    .q_o(state_error_q)
  );

  `ASSERT(InsnAlwaysValidInStall, state_q == OtbnStateStall |-> insn_valid_i)

  // Anything that moves us or keeps us in the stall state should cause `stall` to be asserted
  `ASSERT(StallIfNextStateStall, insn_valid_i & (state_d == OtbnStateStall) |-> stall)

  // The raw signal is needed by the instruction fetch stage for generating instruction address
  // errors (where instruction fetch and prefetch disagree on address). `err` will factor this in so
  // using the qualified signal results in a combinational loop.
  assign insn_fetch_req_valid_raw_o = insn_fetch_req_valid_raw;
  assign insn_fetch_req_valid_o     = err ? 1'b0 : insn_fetch_req_valid_raw;

  // Determine if there are any errors related to the Imem fetch address.
  always_comb begin
    imem_addr_err = 1'b0;

    if (insn_fetch_req_valid_raw) begin
      if (|insn_fetch_req_addr_o[1:0]) begin
        // Imem address is unaligned
        imem_addr_err = 1'b1;
      end else if (branch_taken) begin
        imem_addr_err = branch_target_overflow;
      end else begin
        imem_addr_err = next_insn_addr_wide[ImemAddrWidth] & insn_valid_i;
      end
    end
  end

  // Signal error if MuBi input signals take on invalid values as this means something bad is
  // happening. Register the error signal to break circular paths (instruction fetch errors factor
  // into fatal_escalate_en_i, RND errors factor into recov_escalate_en_i).
  assign mubi_err_d = |{mubi4_test_invalid(fatal_escalate_en_i),
                        mubi4_test_invalid(recov_escalate_en_i),
                        mubi4_test_invalid(rma_req_i),
                        mubi_err_q};
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mubi_err_q <= 1'b0;
    end else begin
      mubi_err_q <= mubi_err_d;
    end
  end

  // Instruction is illegal based on the static properties of the instruction bits (illegal encoding
  // or illegal WSR/CSR referenced).
  assign illegal_insn_static = insn_illegal_i | ispr_err;

  assign fatal_software_err       = software_err & software_errs_fatal_i;
  assign bad_internal_state_err   = |{state_error_d, loop_hw_err, rf_base_call_stack_hw_err_i,
                                      rf_bignum_spurious_we_err, spurious_secure_wipe_ack_q,
                                      mubi_err_q};
  assign reg_intg_violation_err   = rf_bignum_intg_err | ispr_rdata_intg_err;
  assign key_invalid_err          = ispr_rd_bignum_insn & insn_valid_i & key_invalid;
  assign illegal_insn_err         = illegal_insn_static | rf_indirect_err;
  assign call_stack_sw_err        = rf_base_call_stack_sw_err_i;

  // Flag a bad data address error if the data memory address is invalid and it does not come from
  // an empty call stack.  The second case cannot be decided as bad data address because the address
  // on top of the empty call stack may or may not be valid.  (Also, in most RTL simulators an empty
  // call stack that has never been pushed contains an unknown value, so this error bit would become
  // unknown.)  Thus, a data memory address coming from an empty call stack raises a call stack
  // error but never a bad data address error.
  assign bad_data_addr_err = dmem_addr_err &
                             ~(call_stack_sw_err &
                               (ld_insn_with_addr_from_call_stack |
                                st_insn_with_addr_from_call_stack));

  // Identify load instructions that take the memory address from the call stack.
  assign ld_insn_with_addr_from_call_stack = insn_valid_i               &
                                             insn_dec_shared_i.ld_insn  &
                                             insn_dec_base_i.rf_ren_a   &
                                             (insn_dec_base_i.a == 5'd1);

  // Identify store instructions that take the memory address from the call stack.
  assign st_insn_with_addr_from_call_stack = insn_valid_i               &
                                             insn_dec_shared_i.st_insn  &
                                             insn_dec_base_i.rf_ren_a   &
                                             (insn_dec_base_i.a == 5'd1);

  // All software errors that aren't bad_insn_addr. Factored into bad_insn_addr so it is only raised
  // if other software errors haven't ocurred. As bad_insn_addr relates to the next instruction
  // begin fetched it cannot occur if the current instruction has seen an error and failed to
  // execute.
  assign non_insn_addr_software_err = |{key_invalid_err,
                                        loop_sw_err,
                                        illegal_insn_err,
                                        call_stack_sw_err,
                                        bad_data_addr_err};

  assign bad_insn_addr_err = imem_addr_err & ~non_insn_addr_software_err;

  assign err_bits_d = '{
    fatal_software:     fatal_software_err,
    bad_internal_state: bad_internal_state_err,
    reg_intg_violation: reg_intg_violation_err,
    key_invalid:        key_invalid_err,
    loop:               loop_sw_err,
    illegal_insn:       illegal_insn_err,
    call_stack:         call_stack_sw_err,
    bad_data_addr:      bad_data_addr_err,
    bad_insn_addr:      bad_insn_addr_err
  };

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      err_bits_q <= '0;
    end else begin
      if (err_bit_clear_i && !locking_o) begin
        err_bits_q <= '0;
      end else begin
        err_bits_q <= err_bits_q | err_bits_d;
      end
    end
  end
  assign err_bits_o = err_bits_q;

  assign software_err = non_insn_addr_software_err | bad_insn_addr_err;

  assign recoverable_err = mubi4_test_true_loose(recov_escalate_en_i);

  assign internal_fatal_err = |{fatal_software_err,
                                bad_internal_state_err,
                                reg_intg_violation_err};

  // In case of an RMA request, just lock up the controller. This triggers the rotation of the
  // scrambling keys. The start/stop controller takes care of initiating the internal secure wipe
  // and eventually acknowledging the RMA request.
  assign fatal_err = |{internal_fatal_err,
                       mubi4_test_true_loose(fatal_escalate_en_i),
                       mubi4_test_true_loose(rma_req_i)};

  assign recoverable_err_o = recoverable_err | (software_err & ~software_errs_fatal_i);
  assign mems_sec_wipe_o   = (state_d == OtbnStateLocked) & (state_q != OtbnStateLocked);

  assign internal_err = software_err | internal_fatal_err;
  assign err          = software_err | recoverable_err | fatal_err;

  assign prefetch_ignore_errs_o = internal_err;

  // Instructions must not execute if there is an error
  assign insn_executing = insn_valid_i & ~err;

  `ASSERT(ErrBitSetOnErr,
      err & (mubi4_test_false_strict(fatal_escalate_en_i) &
             mubi4_test_false_strict(recov_escalate_en_i) &
             mubi4_test_false_strict(rma_req_i)) |=>
          err_bits_o)
  `ASSERT(ErrSetOnFatalErr, fatal_err |-> err)
  `ASSERT(SoftwareErrIfNonInsnAddrSoftwareErr, non_insn_addr_software_err |-> software_err)

  `ASSERT(ControllerStateValid,
          state_q inside {OtbnStateHalt, OtbnStateRun, OtbnStateStall, OtbnStateLocked})
  // Branch only takes effect in OtbnStateRun so must not go into stall state for branch
  // instructions.
  `ASSERT(NoStallOnBranch,
      insn_valid_i & insn_dec_shared_i.branch_insn |-> state_q != OtbnStateStall)

  // SEC_CM: CONTROLLER.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, otbn_state_e, OtbnStateHalt)

  // SEC_CM: CTRL_FLOW.COUNT
  assign insn_cnt_clear = state_reset_i | (state_q == OtbnStateLocked) | insn_cnt_clear_i;

  always_comb begin
    if (insn_cnt_clear) begin
      insn_cnt_d = 32'd0;
    end else if (insn_executing & ~stall & (insn_cnt_q != 32'hffffffff)) begin
      insn_cnt_d = insn_cnt_q + 32'd1;
    end else begin
      insn_cnt_d = insn_cnt_q;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      insn_cnt_q <= 32'd0;
    end else begin
      insn_cnt_q <= insn_cnt_d;
    end
  end

  assign insn_cnt_o = insn_cnt_q;

  assign loop_reset = state_reset_i | sec_wipe_zero_i;

  otbn_loop_controller #(
    .ImemAddrWidth(ImemAddrWidth)
  ) u_otbn_loop_controller (
    .clk_i,
    .rst_ni,

    .state_reset_i(loop_reset),

    .insn_valid_i,
    .insn_addr_i,
    .next_insn_addr_i(next_insn_addr),

    .loop_start_req_i       (loop_start_req),
    .loop_start_commit_i    (loop_start_commit),
    .loop_bodysize_i        (loop_bodysize),
    .loop_iterations_i      (loop_iterations),
    .loop_end_addr_predec_i (ctrl_flow_target_predec_i),

    .loop_jump_o     (loop_jump),
    .loop_jump_addr_o(loop_jump_addr),

    .sw_err_o     (loop_sw_err),
    .hw_err_o     (loop_hw_err),
    .predec_err_o (loop_predec_err),

    .jump_or_branch_i(jump_or_branch),
    .otbn_stall_i    (stall),

    .prefetch_loop_active_o,
    .prefetch_loop_iterations_o,
    .prefetch_loop_end_addr_o,
    .prefetch_loop_jump_addr_o
  );

  // loop_start_req indicates the instruction wishes to start a loop, loop_start_commit confirms it
  // should occur.
  assign loop_start_req    = insn_valid_i & insn_dec_shared_i.loop_insn;
  assign loop_start_commit = insn_executing;
  assign loop_bodysize     = insn_dec_base_i.loop_bodysize;
  assign loop_iterations   = insn_dec_base_i.loop_immediate ? insn_dec_base_i.i :
                                                              rf_base_rd_data_a_no_intg;

  // Compute increments which can be optionally applied to indirect register accesses and memory
  // addresses in BN.LID/BN.SID/BN.MOVR instructions.
  assign rf_base_rd_data_a_inc           = rf_base_rd_data_a_no_intg[4:0] + 1'b1;
  assign rf_base_rd_data_b_inc           = rf_base_rd_data_b_no_intg[4:0] + 1'b1;
  // We can avoid a full 32-bit adder here because the offset is 32-bit aligned, so we know the
  // load/store address will only be valid if rf_base_rd_data_a_no_intg[4:0] is zero.
  assign rf_base_rd_data_a_wlen_word_inc = rf_base_rd_data_a_no_intg[31:5] + 27'h1;

  // Choose increment to write back to base register file, only one increment can be written as
  // there is only one write port. Note that where an instruction is incrementing the indirect
  // reference to its destination register (insn_dec_bignum_i.d_inc) that reference is read on the
  // B read port so the B increment is written back.
  always_comb begin
    unique case (1'b1)
      insn_dec_bignum_i.a_inc: begin
        increment_out = {26'b0, rf_base_rd_data_a_inc};
      end
      insn_dec_bignum_i.b_inc: begin
        increment_out = {26'b0, rf_base_rd_data_b_inc};
      end
      insn_dec_bignum_i.d_inc: begin
        increment_out = {26'b0, rf_base_rd_data_b_inc};
      end
      insn_dec_bignum_i.a_wlen_word_inc: begin
        increment_out = {rf_base_rd_data_a_wlen_word_inc, 5'b0};
      end
      default: begin
        // Whenever increment_out is written back to the register file, exactly one of the
        // increment selector signals is high. To prevent the automatic inference of latches in
        // case nothing is written back (rf_wdata_sel != RfWdSelIncr) and to save logic, we choose
        // a valid output as default.
        increment_out = {26'b0, rf_base_rd_data_a_inc};
      end
    endcase
  end

  // Base RF read/write address, enable and commit control
  always_comb begin
    rf_base_rd_addr_a_o = insn_dec_base_i.a;
    rf_base_rd_addr_b_o = insn_dec_base_i.b;
    rf_base_wr_addr_o   = insn_dec_base_i.d;

    // Only commit read or write if the instruction is executing (in particular a read commit pops
    // the call stack so must not occur where a valid instruction sees an error and doesn't
    // execute).
    rf_base_rd_commit_o = insn_executing;
    rf_base_wr_commit_o = insn_executing;

    rf_base_rd_en_a_raw = 1'b0;
    rf_base_rd_en_b_raw = 1'b0;
    rf_base_wr_en_raw   = 1'b0;

    if (insn_valid_i) begin
      if (insn_dec_shared_i.st_insn) begin
        // For stores, both base reads happen in the first cycle of the store instruction. For base
        // stores this is the same cycle as the request. For bignum stores this is the cycle before
        // the request (as the indirect register read to get the store data occurs the following
        // cycle).
        rf_base_rd_en_a_raw = insn_dec_base_i.rf_ren_a &
          (rf_indirect_stall | (insn_dec_shared_i.subset == InsnSubsetBase));
        rf_base_rd_en_b_raw = insn_dec_base_i.rf_ren_b &
          (rf_indirect_stall | (insn_dec_shared_i.subset == InsnSubsetBase));

        // Bignum stores can update the base register file where an increment is used.
        rf_base_wr_en_raw   = (insn_dec_shared_i.subset == InsnSubsetBignum) &
                              insn_dec_base_i.rf_we                          &
                              rf_indirect_stall;
      end else if (insn_dec_shared_i.ld_insn) begin
        // For loads, both base reads happen in the same cycle as the request. The address is
        // required for the request and the indirect destination register (only used for Bignum
        // loads) is flopped in ld_insn_bignum_wr_addr_q to correctly deal with the case where it's
        // updated by an increment.
        rf_base_rd_en_a_raw = insn_dec_base_i.rf_ren_a & lsu_load_req_raw;
        rf_base_rd_en_b_raw = insn_dec_base_i.rf_ren_b & lsu_load_req_raw;

        if (insn_dec_shared_i.subset == InsnSubsetBignum) begin
          // Bignum loads can update the base register file where an increment is used. This must
          // always happen in the same cycle as the request as this is where both registers are
          // read.
          rf_base_wr_en_raw = insn_dec_base_i.rf_we & lsu_load_req_raw & rf_indirect_stall;
        end else begin
          // For Base loads write the base register file when the instruction is unstalled (meaning
          // the load data is available).
          rf_base_wr_en_raw = insn_dec_base_i.rf_we & ~stall;
        end
      end else if (insn_dec_bignum_i.rf_wdata_sel == RfWdSelMovSel) begin
        // For MOVR base register reads occur in the first cycle of the instruction. The indirect
        // register read for the bignum data occurs in the following cycle.
        rf_base_rd_en_a_raw = insn_dec_base_i.rf_ren_a & rf_indirect_stall;
        rf_base_rd_en_b_raw = insn_dec_base_i.rf_ren_b & rf_indirect_stall;
        rf_base_wr_en_raw   = insn_dec_base_i.rf_we    & rf_indirect_stall;
      end else begin
        // For all other instructions the read and write happen when the instruction is unstalled.
        rf_base_rd_en_a_raw = insn_dec_base_i.rf_ren_a & ~stall;
        rf_base_rd_en_b_raw = insn_dec_base_i.rf_ren_b & ~stall;
        rf_base_wr_en_raw   = insn_dec_base_i.rf_we    & ~stall;
      end
    end

    if (insn_dec_shared_i.subset == InsnSubsetBignum) begin
      unique case (1'b1)
        insn_dec_bignum_i.a_inc,
        insn_dec_bignum_i.a_wlen_word_inc: begin
          rf_base_wr_addr_o = insn_dec_base_i.a;
        end

        insn_dec_bignum_i.b_inc,
        insn_dec_bignum_i.d_inc: begin
          rf_base_wr_addr_o = insn_dec_base_i.b;
        end
        default: ;
      endcase
    end

    rf_base_rd_en_a_o = rf_base_rd_en_a_raw & ~illegal_insn_static;
    rf_base_rd_en_b_o = rf_base_rd_en_b_raw & ~illegal_insn_static;
    rf_base_wr_en_o   = rf_base_wr_en_raw   & ~illegal_insn_static;
  end

  // Base ALU Operand A MUX
  always_comb begin
    unique case (insn_dec_base_i.op_a_sel)
      OpASelRegister: alu_base_operation_o.operand_a = rf_base_rd_data_a_no_intg;
      OpASelZero:     alu_base_operation_o.operand_a = '0;
      OpASelCurrPc:   alu_base_operation_o.operand_a = {{(32 - ImemAddrWidth){1'b0}}, insn_addr_i};
      default:        alu_base_operation_o.operand_a = rf_base_rd_data_a_no_intg;
    endcase
  end

  // Base ALU Operand B MUX
  always_comb begin
    unique case (insn_dec_base_i.op_b_sel)
      OpBSelRegister:  alu_base_operation_o.operand_b = rf_base_rd_data_b_no_intg;
      OpBSelImmediate: alu_base_operation_o.operand_b = insn_dec_base_i.i;
      default:         alu_base_operation_o.operand_b = rf_base_rd_data_b_no_intg;
    endcase
  end

  assign alu_base_operation_o.op = insn_dec_base_i.alu_op;

  assign alu_base_comparison_o.operand_a = rf_base_rd_data_a_no_intg;
  assign alu_base_comparison_o.operand_b = rf_base_rd_data_b_no_intg;
  assign alu_base_comparison_o.op = insn_dec_base_i.comparison_op;

  assign rf_base_rd_data_a_no_intg = rf_base_rd_data_a_intg_i[31:0];
  assign rf_base_rd_data_b_no_intg = rf_base_rd_data_b_intg_i[31:0];

  // TODO: For now integrity bits from RF base are ignored in the controller, remove this when end
  // to end integrity features that use them are implemented
  logic unused_rf_base_rd_a_intg_bits;
  logic unused_rf_base_rd_b_intg_bits;

  assign unused_rf_base_rd_a_intg_bits = |rf_base_rd_data_a_intg_i[38:32];
  assign unused_rf_base_rd_b_intg_bits = |rf_base_rd_data_b_intg_i[38:32];

  // Base register file write MUX. Depending on the data source, integrity bits do or don't have to
  // be appended:
  // - Data sources that require appending integrity bits go into `rf_base_wr_data_no_intg_o` and
  //   `rf_base_wr_data_intg_sel_o` is low.
  // - Data sources that already come with integrity bits go into `rf_base_wr_data_intg_o` and
  //   `rf_base_wr_data_intg_sel_o` is high.
  always_comb begin
    // Default values
    rf_base_wr_data_no_intg_o  = alu_base_operation_result_i;
    rf_base_wr_data_intg_o     = '0;
    rf_base_wr_data_intg_sel_o = 1'b0;

    unique case (insn_dec_base_i.rf_wdata_sel)
      RfWdSelEx: begin
        rf_base_wr_data_no_intg_o  = alu_base_operation_result_i;
      end
      RfWdSelNextPc: begin
        rf_base_wr_data_no_intg_o  = {{(32-(ImemAddrWidth+1)){1'b0}}, next_insn_addr_wide};
      end
      RfWdSelIspr: begin
        rf_base_wr_data_no_intg_o  = csr_rdata;
      end
      RfWdSelIncr: begin
        rf_base_wr_data_no_intg_o  = increment_out;
      end
      RfWdSelLsu: begin
        rf_base_wr_data_intg_sel_o = 1'b1;
        rf_base_wr_data_intg_o     = lsu_base_rdata_i;
      end
      default: ;
    endcase
  end

  for (genvar i = 0; i < BaseWordsPerWLEN; ++i) begin : g_rf_bignum_rd_data
    assign rf_bignum_rd_data_a_no_intg[i*32+:32] = rf_bignum_rd_data_a_intg_i[i*39+:32];
    assign rf_bignum_rd_data_b_no_intg[i*32+:32] = rf_bignum_rd_data_b_intg_i[i*39+:32];
  end

  // Bignum RF control signals from the controller aren't actually used, instead the predecoded
  // one-hot versions are. The predecoded versions get checked against the signals produced here.
  // Buffer them to ensure they don't get optimised away (with a functionaly correct OTBN they will
  // always be identical).
  assign rf_bignum_rd_addr_a_unbuf = insn_dec_bignum_i.rf_a_indirect ? insn_bignum_rd_addr_a_q :
                                                                       insn_dec_bignum_i.a;

  prim_buf #(
    .Width(WdrAw)
  ) u_rf_bignum_rd_addr_a_buf (
    .in_i (rf_bignum_rd_addr_a_unbuf),
    .out_o(rf_bignum_rd_addr_a_o)
  );

  assign rf_bignum_rd_en_a_unbuf = insn_dec_bignum_i.rf_ren_a & insn_valid_i & ~stall;

  prim_buf #(
    .Width(1)
  ) u_rf_bignum_rd_en_a_buf (
    .in_i (rf_bignum_rd_en_a_unbuf),
    .out_o(rf_bignum_rd_en_a_o)
  );

  assign rf_bignum_rd_addr_b_unbuf = insn_dec_bignum_i.rf_b_indirect ? insn_bignum_rd_addr_b_q :
                                                                       insn_dec_bignum_i.b;

  prim_buf #(
    .Width(WdrAw)
  ) u_rf_bignum_rd_addr_b_buf (
    .in_i (rf_bignum_rd_addr_b_unbuf),
    .out_o(rf_bignum_rd_addr_b_o)
  );

  assign rf_bignum_rd_en_b_unbuf = insn_dec_bignum_i.rf_ren_b & insn_valid_i & ~stall;

  prim_buf #(
    .Width(1)
  ) u_rf_bignum_rd_en_b_buf (
    .in_i (rf_bignum_rd_en_b_unbuf),
    .out_o(rf_bignum_rd_en_b_o)
  );

  assign alu_bignum_operation_o.operand_a = rf_bignum_rd_data_a_no_intg;

  // Base ALU Operand B MUX
  always_comb begin
    unique case (insn_dec_bignum_i.alu_op_b_sel)
      OpBSelRegister:  alu_bignum_operation_o.operand_b = rf_bignum_rd_data_b_no_intg;
      OpBSelImmediate: alu_bignum_operation_o.operand_b = insn_dec_bignum_i.i;
      default:         alu_bignum_operation_o.operand_b = rf_bignum_rd_data_b_no_intg;
    endcase
  end

  assign alu_bignum_operation_o.op          = insn_dec_bignum_i.alu_op;
  assign alu_bignum_operation_o.shift_right = insn_dec_bignum_i.alu_shift_right;
  assign alu_bignum_operation_o.shift_amt   = insn_dec_bignum_i.alu_shift_amt;
  assign alu_bignum_operation_o.flag_group  = insn_dec_bignum_i.alu_flag_group;
  assign alu_bignum_operation_o.sel_flag    = insn_dec_bignum_i.alu_sel_flag;
  assign alu_bignum_operation_o.alu_flag_en = insn_dec_bignum_i.alu_flag_en & insn_valid_i;
  assign alu_bignum_operation_o.mac_flag_en = insn_dec_bignum_i.mac_flag_en & insn_valid_i;

  assign alu_bignum_operation_valid_o  = insn_valid_i;
  assign alu_bignum_operation_commit_o = insn_executing;

  assign mac_bignum_operation_o.operand_a         = rf_bignum_rd_data_a_no_intg;
  assign mac_bignum_operation_o.operand_b         = rf_bignum_rd_data_b_no_intg;
  assign mac_bignum_operation_o.operand_a_qw_sel  = insn_dec_bignum_i.mac_op_a_qw_sel;
  assign mac_bignum_operation_o.operand_b_qw_sel  = insn_dec_bignum_i.mac_op_b_qw_sel;
  assign mac_bignum_operation_o.wr_hw_sel_upper   = insn_dec_bignum_i.mac_wr_hw_sel_upper;
  assign mac_bignum_operation_o.pre_acc_shift_imm = insn_dec_bignum_i.mac_pre_acc_shift;
  assign mac_bignum_operation_o.zero_acc          = insn_dec_bignum_i.mac_zero_acc;
  assign mac_bignum_operation_o.shift_acc         = insn_dec_bignum_i.mac_shift_out;

  assign mac_bignum_en_o     = insn_valid_i & insn_dec_bignum_i.mac_en;
  assign mac_bignum_commit_o = insn_executing;

  // Move / Conditional Select. Only select B register data when a selection instruction is being
  // executed and the selection flag isn't set.

  `ASSERT(SelFlagValid, insn_valid_i & insn_dec_bignum_i.sel_insn |->
    insn_dec_bignum_i.alu_sel_flag inside {FlagC, FlagL, FlagM, FlagZ})

  assign selection_result =
    ~insn_dec_bignum_i.sel_insn | alu_bignum_selection_flag_i ? rf_bignum_rd_data_a_intg_i :
                                                                rf_bignum_rd_data_b_intg_i;

  // Bignum Register file write control

  always_comb begin
    // By default write nothing
    rf_bignum_wr_en_unbuf = 2'b00;

    // Only write if valid instruction wants a bignum rf write and it isn't stalled. If instruction
    // doesn't execute (e.g. due to an error) the write won't commit.
    if (insn_valid_i && insn_dec_bignum_i.rf_we && !rf_indirect_stall) begin
      if (insn_dec_bignum_i.mac_en && insn_dec_bignum_i.mac_shift_out) begin
        // Special handling for BN.MULQACC.SO, only enable upper or lower half depending on
        // mac_wr_hw_sel_upper.
        rf_bignum_wr_en_unbuf = insn_dec_bignum_i.mac_wr_hw_sel_upper ? 2'b10 : 2'b01;
      end else begin
        // For everything else write both halves immediately.
        rf_bignum_wr_en_unbuf = 2'b11;
      end
    end
  end

  // Bignum RF control signals from the controller aren't actually used, instead the predecoded
  // one-hot versions are. The predecoded versions get checked against the signals produced here.
  // Buffer them to ensure they don't get optimised away (with a functionaly correct OTBN they will
  // always be identical).
  prim_buf #(
    .Width(2)
  ) u_bignum_wr_en_buf (
    .in_i (rf_bignum_wr_en_unbuf),
    .out_o(rf_bignum_wr_en_o)
  );


  assign rf_bignum_wr_commit_o = |rf_bignum_wr_en_o & insn_executing & !stall;

  assign rf_bignum_indirect_en_o    = insn_executing & rf_indirect_stall;
  assign rf_bignum_rd_a_indirect_en = insn_executing & insn_dec_bignum_i.rf_a_indirect;
  assign rf_bignum_rd_b_indirect_en = insn_executing & insn_dec_bignum_i.rf_b_indirect;
  assign rf_bignum_wr_indirect_en   = insn_executing & insn_dec_bignum_i.rf_d_indirect;

  prim_onehot_enc #(
    .OneHotWidth(NWdr)
  ) rf_bignum_rd_a_idirect_onehot__enc (
    .in_i  (rf_base_rd_data_a_no_intg[4:0]),
    .en_i  (rf_bignum_rd_a_indirect_en),
    .out_o (rf_bignum_rd_a_indirect_onehot_o)
  );

  prim_onehot_enc #(
    .OneHotWidth(NWdr)
  ) rf_bignum_rd_b_indirect_onehot_enc (
    .in_i  (rf_base_rd_data_b_no_intg[4:0]),
    .en_i  (rf_bignum_rd_b_indirect_en),
    .out_o (rf_bignum_rd_b_indirect_onehot_o)
  );

  prim_onehot_enc #(
    .OneHotWidth(NWdr)
  ) rf_bignum_wr_indirect_onehot_enc (
    .in_i  (rf_base_rd_data_b_no_intg[4:0]),
    .en_i  (rf_bignum_wr_indirect_en),
    .out_o (rf_bignum_wr_indirect_onehot_o)
  );

  // For BN.LID sample the indirect destination register index in first cycle as an increment might
  // change it for the second cycle where the load data is written to the bignum register file.
  always_ff @(posedge clk_i) begin
    if (insn_dec_bignum_i.rf_d_indirect) begin
      insn_bignum_wr_addr_q <= rf_base_rd_data_b_no_intg[4:0];
    end

    if (insn_dec_bignum_i.rf_a_indirect) begin
      insn_bignum_rd_addr_a_q <= rf_base_rd_data_a_no_intg[4:0];
    end

    if (insn_dec_bignum_i.rf_b_indirect) begin
      insn_bignum_rd_addr_b_q <= rf_base_rd_data_b_no_intg[4:0];
    end
  end

  // Bignum RF control signals from the controller aren't actually used, instead the predecoded
  // one-hot versions are. The predecoded versions get checked against the signals produced here.
  // Buffer them to ensure they don't get optimised away (with a functionaly correct OTBN they will
  // always be identical).
  assign rf_bignum_wr_addr_unbuf = insn_dec_bignum_i.rf_d_indirect ? insn_bignum_wr_addr_q :
                                                                     insn_dec_bignum_i.d;

  prim_buf #(
    .Width(WdrAw)
  ) u_rf_bignum_wr_addr_buf (
    .in_i (rf_bignum_wr_addr_unbuf),
    .out_o(rf_bignum_wr_addr_o)
  );

  // For the shift-out variant of BN.MULQACC the bottom half of the MAC result is written to one
  // half of a desintation register specified by the instruction (mac_wr_hw_sel_upper). The bottom
  // half of the MAC result must be placed in the appropriate half of the write data (the RF only
  // accepts write data for the top half in the top half of the write data input). Otherwise
  // (shift-out to bottom half and all other BN.MULQACC instructions) simply pass the MAC result
  // through unchanged as write data.
  assign mac_bignum_rf_wr_data[WLEN-1:WLEN/2] =
      insn_dec_bignum_i.mac_wr_hw_sel_upper &&
      insn_dec_bignum_i.mac_shift_out          ? mac_bignum_operation_result_i[WLEN/2-1:0] :
                                                 mac_bignum_operation_result_i[WLEN-1:WLEN/2];

  assign mac_bignum_rf_wr_data[WLEN/2-1:0] = mac_bignum_operation_result_i[WLEN/2-1:0];

  // Bignum register file write MUX. Depending on the data source, integrity bits do or don't have
  // to be appended; see comments on the "Base register file write MUX" for details.
  always_comb begin
    // Default values
    rf_bignum_wr_data_intg_sel_o = 1'b0;
    rf_bignum_wr_data_intg_o     = '0;
    rf_bignum_wr_data_no_intg_o  = alu_bignum_operation_result_i;

    unique case (insn_dec_bignum_i.rf_wdata_sel)
      RfWdSelEx: begin
        rf_bignum_wr_data_no_intg_o  = alu_bignum_operation_result_i;
      end
      RfWdSelMac: begin
        rf_bignum_wr_data_no_intg_o  = mac_bignum_rf_wr_data;
      end
      RfWdSelIspr: begin
        rf_bignum_wr_data_intg_sel_o = 1'b1;
        rf_bignum_wr_data_intg_o     = ispr_rdata_intg_i;
      end
      RfWdSelMovSel: begin
        rf_bignum_wr_data_intg_sel_o = 1'b1;
        rf_bignum_wr_data_intg_o     = selection_result;
      end
      RfWdSelLsu: begin
        rf_bignum_wr_data_intg_sel_o = 1'b1;
        //SEC_CM: BUS.INTEGRITY
        rf_bignum_wr_data_intg_o     = lsu_bignum_rdata_i;
      end
      default: ;
    endcase
  end

  assign rf_a_indirect_err = insn_dec_bignum_i.rf_a_indirect    &
                             (|rf_base_rd_data_a_no_intg[31:5]) &
                             ~rf_base_call_stack_sw_err_i       &
                             rf_base_rd_en_a_o;

  assign rf_b_indirect_err = insn_dec_bignum_i.rf_b_indirect    &
                             (|rf_base_rd_data_b_no_intg[31:5]) &
                             ~rf_base_call_stack_sw_err_i       &
                             rf_base_rd_en_b_o;

  assign rf_d_indirect_err = insn_dec_bignum_i.rf_d_indirect    &
                             (|rf_base_rd_data_b_no_intg[31:5]) &
                             ~rf_base_call_stack_sw_err_i       &
                             rf_base_rd_en_b_o;

  assign rf_indirect_err =
      insn_valid_i & (rf_a_indirect_err | rf_b_indirect_err | rf_d_indirect_err);


  // If the source registers are indirectly indexed and there is a stack error, the source
  // register indices were illegal due to a stack pop error. In this case, ignore bignum RF read
  // integrity errors.
  assign ignore_rf_bignum_intg_errs = (insn_dec_bignum_i.rf_a_indirect |
                                       insn_dec_bignum_i.rf_b_indirect) &
                                      rf_base_call_stack_sw_err_i;

  assign rf_bignum_intg_err = rf_bignum_intg_err_i & ~ignore_rf_bignum_intg_errs;

  // If the destination register is indirectly indexed and there is a stack error, the destination
  // register index was illegal due to a stack pop error. In this case, ignore bignum RF
  // write-enable errors.
  assign ignore_rf_bignum_spurious_we_errs = insn_dec_bignum_i.rf_d_indirect &
                                             rf_base_call_stack_sw_err_i;

  assign rf_bignum_spurious_we_err = rf_bignum_spurious_we_err_i &
                                     ~ignore_rf_bignum_spurious_we_errs;

  // CSR/WSR/ISPR handling
  // ISPRs (Internal Special Purpose Registers) are the internal registers. CSRs and WSRs are the
  // ISA visible versions of those registers in the base and bignum ISAs respectively.

  assign csr_addr     = csr_e'(insn_dec_base_i.i[11:0]);
  assign csr_sub_addr = insn_dec_base_i.i[$clog2(BaseWordsPerWLEN)-1:0];

  always_comb begin
    ispr_addr_base      = IsprMod;
    ispr_word_addr_base = '0;
    csr_illegal_addr    = 1'b0;

    unique case (csr_addr)
      CsrFlags, CsrFg0, CsrFg1: begin
        ispr_addr_base      = IsprFlags;
        ispr_word_addr_base = '0;
      end
      CsrMod0, CsrMod1, CsrMod2, CsrMod3, CsrMod4, CsrMod5, CsrMod6, CsrMod7: begin
        ispr_addr_base      = IsprMod;
        ispr_word_addr_base = csr_sub_addr;
      end
      CsrRndPrefetch: begin
        // Reading from RND_PREFETCH results in 0, there is no ISPR to read so no address is set.
        // The csr_rdata mux logic takes care of producing the 0.
      end
      CsrRnd: begin
        ispr_addr_base      = IsprRnd;
        ispr_word_addr_base = '0;
      end
      CsrUrnd: begin
        ispr_addr_base      = IsprUrnd;
        ispr_word_addr_base = '0;
      end
      default: csr_illegal_addr = 1'b1;
    endcase
  end

  for (genvar i_word = 0; i_word < BaseWordsPerWLEN; i_word++) begin : g_ispr_word_sel_base
    assign ispr_word_sel_base[i_word] = ispr_word_addr_base == i_word;
  end

  // Decode wide ISPR read data.
  logic [WLEN-1:0]                ispr_rdata;
  logic [2*BaseWordsPerWLEN-1:0]  ispr_rdata_intg_err_wide;
  logic [BaseWordsPerWLEN-1:0]    ispr_rdata_intg_err_narrow;
  for (genvar i_word = 0; i_word < BaseWordsPerWLEN; i_word++) begin : g_ispr_rdata_dec
    prim_secded_inv_39_32_dec i_secded_dec (
      .data_i     (ispr_rdata_intg_i[i_word*39+:39]),
      .data_o     (/* unused because we abort on any integrity error */),
      .syndrome_o (/* unused */),
      .err_o      (ispr_rdata_intg_err_wide[i_word*2+:2])
    );
    assign ispr_rdata[i_word*32+:32] = ispr_rdata_intg_i[i_word*39+:32];
    assign ispr_rdata_intg_err_narrow[i_word] = |(ispr_rdata_intg_err_wide[i_word*2+:2]);
  end

  // Propagate integrity error only if wide ISPR is used.

  // Handle ISPR integrity error detection. We've got a bitmask of ISPR words that failed their
  // integrity check (ispr_rdata_intg_err_narrow), but a nonzero entry may not be a problem if we
  // don't actually use the data.
  //
  // The situations when the data is actually used are:
  //
  //   (1) This is a bignum instruction that writes back to the bignum register file by reading an
  //       ISPR. In this case, we actually pass the data through with integrity bits, but it
  //       shouldn't hurt to add fault detection at this point.
  //
  //   (2) This instruction consumes the data by selecting a word from an ISPR and then writing it
  //       back. This happens for things like CSRRS instructions, where the data flows to the base
  //       register file through rf_base_wr_data_no_intg_o and back to the ISPR through
  //       ispr_base_wdata_o. The word used is given by the onehot ispr_word_sel_base mask.
  //
  // In both cases, there's a special case for the RND_PREFETCH register, which doesn't actually
  // have any backing data. It reads as zero with invalid integrity bits which we want to ignore.

  // Are we reading all the ISPR data? (case (1) above)
  logic all_ispr_words_used;
  assign all_ispr_words_used = (insn_dec_bignum_i.rf_wdata_sel == RfWdSelIspr);

  // Are we reading just one word of the ISPR data? (case (2) above).
  logic one_ispr_word_used;
  assign one_ispr_word_used = ispr_rd_insn & (insn_dec_shared_i.subset == InsnSubsetBase);

  // A bit-mask giving which ISPR words are being read
  logic [BaseWordsPerWLEN-1:0] ispr_read_mask;
  assign ispr_read_mask = all_ispr_words_used ? '1 :
                          one_ispr_word_used  ? ispr_word_sel_base : '0;

  // Use ispr_read_mask to qualify the error bit-mask that came out of the integrity decoder.
  logic [BaseWordsPerWLEN-1:0] ispr_rdata_used_intg_err;
  assign ispr_rdata_used_intg_err = ispr_read_mask & ispr_rdata_intg_err_narrow;

  // We only architecturally read the ISPR when there's a non-stalled instruction. This is also the
  // place where we factor in the special RND_PREFETCH behaviour. We also need to squash any
  // integrity errors if we're reading a sideload key which isn't currently valid (this will
  // generate a key_invalid error, but we shouldn't have any behaviour that depends on what happens
  // to be on the pins)
  logic non_prefetch_insn_running;
  assign non_prefetch_insn_running = (insn_valid_i & ~stall &
                                      (csr_addr != CsrRndPrefetch) & ~key_invalid);

  assign ispr_rdata_intg_err = non_prefetch_insn_running & |(ispr_rdata_used_intg_err);

  `ASSERT_KNOWN(IsprRdataIntgErrKnown_A, ispr_rdata_intg_err)

  for (genvar i_bit = 0; i_bit < 32; i_bit++) begin : g_csr_rdata_mux
    for (genvar i_word = 0; i_word < BaseWordsPerWLEN; i_word++) begin : g_csr_rdata_mux_inner
      assign csr_rdata_mux[i_bit][i_word] =
          ispr_rdata[i_word*32 + i_bit] & ispr_word_sel_base[i_word];
    end

    assign csr_rdata_raw[i_bit] = |csr_rdata_mux[i_bit];
  end

  // Specialised read data handling for CSR reads where raw read data needs modification.
  always_comb begin
    csr_rdata = csr_rdata_raw;

    unique case (csr_addr)
      // For FG0/FG1 select out appropriate bits from FLAGS ISPR and pad the rest with zeros.
      CsrFg0:         csr_rdata = {28'b0, csr_rdata_raw[3:0]};
      CsrFg1:         csr_rdata = {28'b0, csr_rdata_raw[7:4]};
      CsrRndPrefetch: csr_rdata = '0;
      default: ;
    endcase
  end

  assign csr_wdata_raw = insn_dec_shared_i.ispr_rs_insn ? csr_rdata | rf_base_rd_data_a_no_intg :
                                                          rf_base_rd_data_a_no_intg;

  // Specialised write data handling for CSR writes where raw write data needs modification.
  always_comb begin
    csr_wdata = csr_wdata_raw;

    unique case (csr_addr)
      // For FG0/FG1 only modify relevant part of FLAGS ISPR.
      CsrFg0: csr_wdata = {24'b0, csr_rdata_raw[7:4], csr_wdata_raw[3:0]};
      CsrFg1: csr_wdata = {24'b0, csr_wdata_raw[3:0], csr_rdata_raw[3:0]};
      default: ;
    endcase
  end

  // ISPR RS (read and set) must not be combined with ISPR RD or WR (read or write). ISPR RD and
  // WR (read and write) is allowed.
  `ASSERT(NoIsprRorWAndRs, insn_valid_i |-> ~(insn_dec_shared_i.ispr_rs_insn   &
                                              (insn_dec_shared_i.ispr_rd_insn |
                                               insn_dec_shared_i.ispr_wr_insn)))


  assign wsr_addr = wsr_e'(insn_dec_bignum_i.i[WsrNumWidth-1:0]);

  always_comb begin
    ispr_addr_bignum = IsprMod;
    wsr_illegal_addr = 1'b0;
    key_invalid      = 1'b0;

    unique case (wsr_addr)
      WsrMod:  ispr_addr_bignum = IsprMod;
      WsrRnd:  ispr_addr_bignum = IsprRnd;
      WsrUrnd: ispr_addr_bignum = IsprUrnd;
      WsrAcc:  ispr_addr_bignum = IsprAcc;
      WsrKeyS0L: begin
        ispr_addr_bignum = IsprKeyS0L;
        key_invalid = ~sideload_key_shares_valid_i[0];
      end
      WsrKeyS0H: begin
        ispr_addr_bignum = IsprKeyS0H;
        key_invalid = ~sideload_key_shares_valid_i[0];
      end
      WsrKeyS1L: begin
        ispr_addr_bignum = IsprKeyS1L;
        key_invalid = ~sideload_key_shares_valid_i[1];
      end
      WsrKeyS1H: begin
        ispr_addr_bignum = IsprKeyS1H;
        key_invalid = ~sideload_key_shares_valid_i[1];
      end
      default: wsr_illegal_addr = 1'b1;
    endcase
  end

  assign wsr_wdata = insn_dec_shared_i.ispr_rs_insn ? ispr_rdata | rf_bignum_rd_data_a_no_intg :
                                                      rf_bignum_rd_data_a_no_intg;

  assign ispr_illegal_addr = insn_dec_shared_i.subset == InsnSubsetBase ? csr_illegal_addr :
                                                                          wsr_illegal_addr;

  assign ispr_err = ispr_illegal_addr & insn_valid_i & (insn_dec_shared_i.ispr_rd_insn |
                                                        insn_dec_shared_i.ispr_wr_insn |
                                                        insn_dec_shared_i.ispr_rs_insn);

  assign ispr_wr_insn = insn_dec_shared_i.ispr_wr_insn | insn_dec_shared_i.ispr_rs_insn;
  assign ispr_rd_insn = insn_dec_shared_i.ispr_rd_insn | insn_dec_shared_i.ispr_rs_insn;

  // Write to RND_PREFETCH must not produce ISR write
  assign ispr_wr_base_insn =
    ispr_wr_insn & (insn_dec_shared_i.subset == InsnSubsetBase) & (csr_addr != CsrRndPrefetch);

  assign ispr_wr_bignum_insn = ispr_wr_insn & (insn_dec_shared_i.subset == InsnSubsetBignum);
  assign ispr_rd_bignum_insn = ispr_rd_insn & (insn_dec_shared_i.subset == InsnSubsetBignum);

  assign ispr_addr_o         = insn_dec_shared_i.subset == InsnSubsetBase ? ispr_addr_base :
                                                                            ispr_addr_bignum;
  assign ispr_base_wdata_o   = csr_wdata;
  assign ispr_base_wr_en_o   = {BaseWordsPerWLEN{ispr_wr_base_insn & insn_valid_i}} &
                               ispr_word_sel_base;

  for (genvar i_word = 0; i_word < BaseWordsPerWLEN; i_word++) begin : g_ispr_bignum_wdata_enc
    prim_secded_inv_39_32_enc i_secded_enc (
      .data_i(wsr_wdata[i_word*32+:32]),
      .data_o(ispr_bignum_wdata_intg_o[i_word*39+:39])
    );
  end
  assign ispr_bignum_wr_en_o = ispr_wr_bignum_insn & insn_valid_i;

  assign ispr_wr_commit_o = ispr_wr_insn & insn_executing;
  assign ispr_rd_en_o     = ispr_rd_insn & insn_valid_i &
    ~((insn_dec_shared_i.subset == InsnSubsetBase) & (csr_addr == CsrRndPrefetch));

  // For BN.SID the LSU address is computed in the first cycle by the base ALU. The store request
  // itself occurs in the second cycle when the store data is available (from the indirect register
  // read). The calculated address is saved in a flop here so it's available for use in the second
  // cycle.
  assign lsu_addr_saved_d = alu_base_operation_result_i[DmemAddrWidth-1:0];
  always_ff @(posedge clk_i) begin
    lsu_addr_saved_q <= lsu_addr_saved_d;
  end

  //assign expected_lsu_addr_en_predec = insn_valid & insn_dec_shared_i.ld_insn

  // lsu_load_req_raw/lsu_store_req_raw indicate an instruction wishes to perform a store or a load.
  // lsu_load_req_o/lsu_store_req_o factor in whether an instruction is actually executing (it may
  // be suppressed due an error) and command the load or store to happen when asserted.
  assign lsu_load_req_raw = insn_valid_i & insn_dec_shared_i.ld_insn & (state_q == OtbnStateRun);
  assign lsu_load_req_o   = insn_executing & lsu_load_req_raw;

  assign lsu_store_req_raw = insn_valid_i & insn_dec_shared_i.st_insn & ~rf_indirect_stall;
  assign lsu_store_req_o   = insn_executing & lsu_store_req_raw;

  assign lsu_req_subset_o = insn_dec_shared_i.subset;

  // To simplify blanking logic all two cycle memory operations (BN.LID, BN.SID, LW) present the
  // calculated address in their first cycle and the saved address in the second cycle. This results
  // in lsu_addr_o remaining stable for the entire instruction. Only SW is a single cycle
  // instruction so it only presents the calculated address. The stability property is checked by an
  // assertion.
  assign lsu_addr_saved_sel =
    insn_valid_i & ((insn_dec_shared_i.subset == InsnSubsetBignum) ||
                    insn_dec_shared_i.ld_insn                         ? ~stall : 1'b0);

  assign lsu_addr = lsu_addr_saved_sel ? lsu_addr_saved_q                                :
                                         alu_base_operation_result_i[DmemAddrWidth-1:0];

  // SEC_CM: CTRL.REDUN
  assign expected_lsu_addr_en =
    insn_valid_i & (insn_dec_shared_i.ld_insn | insn_dec_shared_i.st_insn);

  assign lsu_predec_error = expected_lsu_addr_en != lsu_addr_en_predec_i;

  assign expected_call_stack_push =
    insn_valid_i & insn_dec_base_i.rf_we & rf_base_wr_addr_o == 5'd1;

  assign expected_call_stack_pop = insn_valid_i &
                                   ((insn_dec_base_i.rf_ren_a & rf_base_rd_addr_a_o == 5'd1) |
                                    (insn_dec_base_i.rf_ren_b & rf_base_rd_addr_b_o == 5'd1));

  // Check branch target against the precalculated target from pre-decode. Pre-decode cannot
  // calculate the jump target of a JALR as it requires a register read so this is excluded from the
  // check (by looking at the ALU op a selection).
  assign branch_target_predec_error =
    insn_dec_shared_i.branch_insn                                            &
    insn_dec_shared_i.jump_insn & insn_dec_base_i.op_a_sel != OpASelRegister &
    (ctrl_flow_target_predec_i != branch_target);

  assign ctrl_predec_error =
    |{ctrl_flow_predec_i.jump_insn       != (insn_dec_shared_i.jump_insn   & insn_valid_i),
      ctrl_flow_predec_i.loop_insn       != (insn_dec_shared_i.loop_insn   & insn_valid_i),
      ctrl_flow_predec_i.branch_insn     != (insn_dec_shared_i.branch_insn & insn_valid_i),
      ctrl_flow_predec_i.call_stack_push != expected_call_stack_push,
      ctrl_flow_predec_i.call_stack_pop  != expected_call_stack_pop,
      branch_target_predec_error,
      loop_predec_err};

  assign predec_error_o = lsu_predec_error | ctrl_predec_error;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(DmemAddrWidth)) u_lsu_addr_blanker (
    .in_i (lsu_addr),
    .en_i (lsu_addr_en_predec_i),
    .out_o(lsu_addr_blanked)
  );

  // Check stability property described above (see the lsu_addr_saved_sel signal) holds.
  `ASSERT(LsuAddrBlankedStable_A, insn_valid_i & stall & ~err |=> $stable(lsu_addr_blanked))

  assign lsu_addr_o = lsu_addr_blanked;

  assign lsu_base_wdata_o   = rf_base_rd_data_b_intg_i;
  assign lsu_bignum_wdata_o = rf_bignum_rd_data_b_intg_i;

  assign dmem_addr_unaligned_bignum =
      (lsu_req_subset_o == InsnSubsetBignum) & (|lsu_addr_o[$clog2(WLEN/8)-1:0]);
  assign dmem_addr_unaligned_base   =
      (lsu_req_subset_o == InsnSubsetBase)   & (|lsu_addr_o[1:0]);
  assign dmem_addr_overflow         = |alu_base_operation_result_i[31:DmemAddrWidth];

  // A dmem address is checked the cycle it is available. For bignum stores this is the first cycle
  // where the base register file read occurs, with the store request occurring the following cycle.
  // For all other loads and stores the dmem address is available the same cycle as the request.
  assign dmem_addr_err_check =
    (lsu_req_subset_o == InsnSubsetBignum) &
    insn_dec_shared_i.st_insn               ? rf_indirect_stall :
                                              lsu_load_req_raw | lsu_store_req_raw;

  assign dmem_addr_err =
      insn_valid_i & dmem_addr_err_check & (dmem_addr_overflow         |
                                            dmem_addr_unaligned_bignum |
                                            dmem_addr_unaligned_base);

  assign rnd_req_raw = insn_valid_i & ispr_rd_insn & (ispr_addr_o == IsprRnd);
  // Don't factor rnd_rep/fips_err_i into rnd_req_o. This would lead to a combo loop.
  assign rnd_req_o = rnd_req_raw & insn_valid_i & ~(software_err | fatal_err);

  assign rnd_prefetch_req_o = insn_executing & ispr_wr_insn &
      (insn_dec_shared_i.subset == InsnSubsetBase) & (csr_addr == CsrRndPrefetch);
endmodule
