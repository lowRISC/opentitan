// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Component handling register CDC

`include "prim_assert.sv"

module prim_reg_cdc #(
  parameter int DataWidth = 32,
  parameter logic [DataWidth-1:0] ResetVal = 32'h0,
  parameter logic [DataWidth-1:0] BitMask = 32'hFFFFFFFF
) (
  input clk_src_i,
  input rst_src_ni,
  input clk_dst_i,
  input rst_dst_ni,

  input src_update_i,
  input src_regwen_i,
  input src_we_i,
  input src_re_i,
  input [DataWidth-1:0] src_wd_i,
  output logic src_busy_o,
  output logic [DataWidth-1:0] src_qs_o,
  input  [DataWidth-1:0] dst_d_i,
  output logic dst_we_o,
  output logic dst_re_o,
  output logic dst_regwen_o,
  output logic [DataWidth-1:0] dst_wd_o
);

  ////////////////////////////
  // Source domain
  ////////////////////////////
  localparam int TxnWidth = 3;

  logic src_ack;
  logic src_busy_q;
  logic [DataWidth-1:0] src_q;
  logic [TxnWidth-1:0] txn_bits_q;
  logic src_req;

  assign src_req = src_we_i | src_re_i;

  // busy indication back-pressures upstream if the register is accessed
  // again.  The busy indication is also used as a "commit" indication for
  // resolving software and hardware write conflicts
  always_ff @(posedge clk_src_i or negedge rst_src_ni) begin
    if (!rst_src_ni) begin
      src_busy_q <= '0;
    end else if (src_req) begin
      src_busy_q <= 1'b1;
    end else if (src_busy_q && src_ack) begin
      src_busy_q <= 1'b0;
    end
  end

  assign src_busy_o = src_busy_q;

  // src_q acts as both the write holding register and the software read back
  // register.
  // When software performs a write, the write data is captured in src_q for
  // CDC purposes.  When not performing a write, the src_q periodically
  // samples the destination domain using the src_update_i indication.
  //
  // To resolve software and hardware conflicts, the process is as follows:
  // When software issues a write, this module asserts "busy".  While busy,
  // src_q does not sample the destination value.  Since the
  // logic has committed to updating based on software command, there is an irreversible
  // window from which hardware writes are ignored.  Once the busy window completes,
  // the cdc portion then begins sampling once more.
  //
  // This is consistent with prim_subreg_arb where during software / hardware conflicts,
  // software is always prioritized.  The main difference is the conflict resolution window
  // is now larger instead of just one destination clock cycle.

  logic busy;
  assign busy = src_busy_q & !src_ack;

  always_ff @(posedge clk_src_i or negedge rst_src_ni) begin
    if (!rst_src_ni) begin
      src_q <= ResetVal;
      txn_bits_q <= '0;
    end else if (src_req && !busy) begin
      src_q <= src_wd_i & BitMask;
      txn_bits_q <= {src_we_i, src_re_i, src_regwen_i};
    end else if (src_busy_q && src_ack || src_update_i && !busy) begin
      // sample data whenever a busy transaction finishes OR
      // when an update pulse is seen.
      // TODO: We should add a cover group to test different sync timings
      // between src_ack and src_update. Ie, there can be 3 scearios:
      // 1. update one cycle before ack
      // 2. ack one cycle before update
      // 3. update / ack on the same cycle
      // During all 3 cases the read data should be correct
      src_q <= dst_d_i;
      txn_bits_q <= '0;
    end
  end

  // reserved bits are not used
  logic unused_wd;
  assign unused_wd = ^src_wd_i;

  // src_q is always updated in the clk_src domain.
  // when performing an update to the destination domain, it is guaranteed
  // to not change by protocol.
  assign src_qs_o = src_q;
  assign dst_wd_o = src_q;

  ////////////////////////////
  // CDC handling
  ////////////////////////////
  logic dst_req;
  prim_sync_reqack u_prim_sync (
    .clk_src_i,
    .rst_src_ni,
    .clk_dst_i,
    .rst_dst_ni,
    .req_chk_i(1'b0),
    // prim_sync_reqack does not natively handle single
    // pulse requests, so use src_busy to even it out.
    .src_req_i(src_req | src_busy_q),
    .src_ack_o(src_ack),
    .dst_req_o(dst_req),
    // immediately ack on destination once request is seen
    .dst_ack_i(dst_req)
  );

  // Each is valid only when destination request pulse is high
  assign {dst_we_o, dst_re_o, dst_regwen_o} = txn_bits_q & {TxnWidth{dst_req}};

  `ASSERT_KNOWN(SrcBusyKnown_A, src_busy_o, clk_src_i, !rst_src_ni)
  `ASSERT_KNOWN(DstReqKnown_A, dst_req, clk_dst_i, !rst_dst_ni)

  // If busy goes high, we must eventually see an ack
  `ASSERT(HungHandShake_A, $rose(src_busy_o) |-> strong(##[0:$] src_ack), clk_src_i, !rst_src_ni)

  `ifdef INC_ASSERT
    logic async_flag;
    always_ff @(posedge clk_src_i or negedge rst_src_ni) begin
      if (!rst_src_ni) begin
        async_flag <= '0;
      end else if (src_req) begin
        async_flag <= 1'b1;
      end else if (dst_req) begin
        async_flag <= '0;
      end
    end

    `ASSERT(ReqTimeout_A, $rose(async_flag) |-> strong(##[0:3] dst_req), clk_dst_i, !rst_dst_ni)
  `endif


endmodule // prim_subreg_cdc
