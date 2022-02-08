// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module implements reset consistency checks
// The main goal is to check whether conditions allow for a reset to be asserted
// For example, if a child reset asserts, it must be the case that its parent
// reset or software controls (if available) have asserted.
// If a child reset asserts and neither of the above case is true, it is considered
// a fatal error.

`include "prim_assert.sv"

module rstmgr_cnsty_chk
  import rstmgr_pkg::*;
  import rstmgr_reg_pkg::*;
(
  input clk_i,
  input rst_ni,
  input child_clk_i,
  input child_rst_ni,
  input parent_rst_ni,
  input sw_rst_req_i,
  output logic sw_rst_req_clr_o,
  output logic err_o,
  output logic fsm_err_o
);

  localparam int MaxSyncDelay = 2;

  // The "+ 2" here is because the cnt counter that uses this width needs to be able to count up to
  // MaxSyncDelay + 1.
  localparam int CntWidth = $clog2(MaxSyncDelay + 2);

  // These two flops below are completely async.
  // The value from these flops are always fed through synchronizers before use.
  logic parent_rst_asserted;
  always_ff @(posedge clk_i or negedge parent_rst_ni) begin
    if (!parent_rst_ni) begin
      parent_rst_asserted <= 1'b1;
    end else begin
      parent_rst_asserted <= '0;
    end
  end

  logic child_rst_asserted;
  always_ff @(posedge clk_i or negedge child_rst_ni) begin
    if (!child_rst_ni) begin
      child_rst_asserted <= 1'b1;
    end else begin
      child_rst_asserted <= '0;
    end
  end

  logic sync_parent_rst;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue(1)
  ) u_parent_sync (
    .clk_i,
    .rst_ni,
    .d_i(parent_rst_asserted),
    .q_o(sync_parent_rst)
  );

  logic sync_child_rst;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue(1)
  ) u_child_sync (
    .clk_i,
    .rst_ni,
    .d_i(child_rst_asserted),
    .q_o(sync_child_rst)
  );

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 7 -n 6 \
  //      -s 90402488 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (57.14%)
  //  4: ||||||||||||||| (42.86%)
  //  5: --
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 5
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    Reset               = 6'b011001,
    Idle                = 6'b111100,
    WaitForParent       = 6'b010010,
    WaitForChild        = 6'b110111,
    WaitForSrcRelease   = 6'b001111,
    WaitForChildRelease = 6'b000100,
    Error               = 6'b101010
  } state_e;

  state_e state_q, state_d;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateWidth-1:0] state_raw_q;
  assign state_q = state_e'(state_raw_q);
  //SEC_CM: LEAF.FSM.SPARSE
  prim_sparse_fsm_flop #(
    .StateEnumT(state_e),
    .Width(StateWidth),
    .ResetValue(StateWidth'(Reset)),
    .EnableAlertTriggerSVA(0)
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .state_i ( state_d     ),
    .state_o ( state_raw_q )
  );

  logic timeout;
  logic cnt_inc;
  logic cnt_clr;
  logic [CntWidth-1:0] cnt;

  // the timeout count is on clk_i because the synchronizers are
  // also operating on clk_i.  We are mainly trying to wait out the reset assertion delays.
  // parent resets are asynchronous assertion so there is at most a one cycle separation.
  // if needed we can make this timeout bigger.
  assign timeout = int'(cnt) > MaxSyncDelay;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= '0;
    end else if (cnt_clr) begin
      cnt <= '0;
    end else if (cnt_inc && !timeout) begin
      cnt <= cnt + 1'b1;
    end
  end

  logic src_valid;
  assign src_valid = sync_parent_rst || sw_rst_req_i;

  logic sync_child_ack;

  // TODO - make this a sparse fsm
  always_comb begin
    state_d = state_q;
    err_o = '0;
    fsm_err_o = '0;
    cnt_inc = '0;
    cnt_clr = '0;
    sw_rst_req_clr_o = '0;

    unique case (state_q)
      Reset: begin
        // when the checker itself comes out of reset, conditions
        // may be ambiguous, wait for things to stabilize
        if (!sync_child_rst && !sync_parent_rst) begin
          state_d = Idle;
        end
      end

      Idle: begin
        // If a child reset asserts, one of the conditions must be true.
        // It is possible for the child to assert but parent to remain de-asserted
        // due to CDC latency (or vice versa), wait for the other corresponding reset
        // when this occurs.
        if (sync_child_rst && src_valid) begin
          state_d = WaitForSrcRelease;
        end else if (sync_child_rst && !sync_parent_rst) begin
          state_d = WaitForParent;
        end else if (sync_parent_rst && !sync_child_rst) begin
          state_d = WaitForChild;
        end
      end

      // parent reset must show up within timeout region
      WaitForParent: begin
        cnt_inc = 1'b1;

        if (timeout && !sync_parent_rst) begin
          state_d = Error;
        end else if (sync_parent_rst) begin
          state_d = WaitForSrcRelease;
          cnt_clr = 1'b1;
        end
      end

      // child reset must show up within timeout region
      WaitForChild: begin
        cnt_inc = 1'b1;

        if (timeout && !sync_child_rst) begin
          state_d = Error;
        end else if (sync_child_rst) begin
          state_d = WaitForSrcRelease;
          cnt_clr = 1'b1;
        end
      end

      // waiting for parent reset to release
      WaitForSrcRelease: begin
        // if arrived here due to software requested reset, it is now
        // okay to clear the original request.
        sw_rst_req_clr_o = 1'b1;

        // it is not possible for the child reset to release
        // ahead of the parent reset
        if (!sync_child_rst && src_valid) begin
          state_d = Error;
        end else if (!src_valid) begin
          cnt_clr = 1'b1;
          state_d = WaitForChildRelease;
        end
      end

      // waiting for child reset to release
      WaitForChildRelease: begin
        // operate only on child ack to keep things in sync
        // This is needed because the reset releases are synchronous to the child clock.
        // So if we have a situation where the child clock is way slower than the local
        // clock used to increment the count, we may timeout incorrectly.
        // By using sync_child_ack, we ensure that the count is advanced only when a
        // child clock edge is seen.  This usage is conservative, because by the time
        // sync_child_ack is seen, there may have been more than one child clock, yet the
        // count is only incremented by 1.
        if (sync_child_ack) begin
          cnt_inc = 1'b1;
          if (sync_child_rst && src_valid) begin
            // This condition covers the case if for whatever reason the parent reset re-asserts
            // in a valid way.
            state_d = WaitForSrcRelease;
            cnt_clr = 1'b1;
          end else if (sync_child_rst && timeout) begin
            state_d = Error;
          end else if (!sync_child_rst) begin
            state_d = Idle;
            cnt_clr = 1'b1;
          end
        end
      end

      Error: begin
        err_o = 1'b1;
      end

      default: begin
        fsm_err_o = 1'b1;
      end
    endcase // unique case (state_q)
  end // always_comb

  logic child_ack;
  prim_sync_reqack u_child_handshake (
    .clk_src_i(clk_i),
    .rst_src_ni(rst_ni),
    .clk_dst_i(child_clk_i),
    .rst_dst_ni(child_rst_ni),
    .req_chk_i('0),
    .src_req_i(1'b1),
    .src_ack_o(sync_child_ack),
    .dst_req_o(child_ack),
    .dst_ack_i(child_ack)
  );


endmodule // rstmgr_cnsty_chk
