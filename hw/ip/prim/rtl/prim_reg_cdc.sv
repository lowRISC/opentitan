// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Component handling register CDC
//
// Currently, this module only works correctly when paired with tlul_adapter_reg.
// This is because tlul_adapter_reg does not emit a new transaction to the same
// register if it discovers it is currently busy. Please see the BusySrcReqChk_A
// assertion below for more details.
//
// If in the future this assumption changes, we can modify this module easily to
// support the new behavior.

`include "prim_assert.sv"

module prim_reg_cdc #(
  parameter int DataWidth = 32,
  parameter logic [DataWidth-1:0] ResetVal = 32'h0,
  parameter logic [DataWidth-1:0] BitMask = 32'hFFFFFFFF,
  // whether this instance needs to support independent hardware writes
  parameter bit DstWrReq = 0
) (
  input clk_src_i,
  input rst_src_ni,
  input clk_dst_i,
  input rst_dst_ni,
  input src_regwen_i,
  input src_we_i,
  input src_re_i,
  input [DataWidth-1:0] src_wd_i,
  output logic src_busy_o,
  output logic [DataWidth-1:0] src_qs_o,
  input  [DataWidth-1:0] dst_ds_i,
  input  [DataWidth-1:0] dst_qs_i,
  input  dst_update_i,
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
    end else if (src_ack) begin
      src_busy_q <= 1'b0;
    end
  end

  // A src_ack should only be sent if there was a src_req.
  // src_busy_q asserts whenever there is a src_req.  By association,
  // whenever src_ack is seen, then src_busy must be high.
  `ASSERT(SrcAckBusyChk_A, src_ack |-> src_busy_q, clk_src_i, !rst_src_ni)

  assign src_busy_o = src_busy_q;

  // src_q acts as both the write holding register and the software read back
  // register.
  // When software performs a write, the write data is captured in src_q for
  // CDC purposes.  When not performing a write, the src_q reflects the most recent
  // hardware value. For registes with no hardware access, this is simply the
  // the value programmed by software (or in the case R1C, W1C etc) the value after
  // the operation. For registers with hardware access, this reflects a potentially
  // delayed version of the real value, as the software facing updates lag real
  // time updates.
  //
  // To resolve software and hardware conflicts, the process is as follows:
  // When software issues a write, this module asserts "busy".  While busy,
  // src_q does not take on destination value updates.  Since the
  // logic has committed to updating based on software command, there is an irreversible
  // window from which hardware writes are ignored.  Once the busy window completes,
  // the cdc portion then begins sampling once more.
  //
  // This is consistent with prim_subreg_arb where during software / hardware conflicts,
  // software is always prioritized.  The main difference is the conflict resolution window
  // is now larger instead of just one destination clock cycle.

  logic busy;
  assign busy = src_busy_q & !src_ack;

  // This is the current destination value
  logic [DataWidth-1:0] dst_qs;
  logic src_update;
  always_ff @(posedge clk_src_i or negedge rst_src_ni) begin
    if (!rst_src_ni) begin
      src_q <= ResetVal;
      txn_bits_q <= '0;
    end else if (src_req) begin
      // See assertion below
      // At the beginning of a software initiated transaction, the following
      // values are captured in the src_q/txn_bits_q flops to ensure they cannot
      // change for the duration of the synchronization operation.
      src_q <= src_wd_i & BitMask;
      txn_bits_q <= {src_we_i, src_re_i, src_regwen_i};
    end else if (src_busy_q && src_ack || src_update && !busy) begin
      // sample data whenever a busy transaction finishes OR
      // when an update pulse is seen.
      // TODO: We should add a cover group to test different sync timings
      // between src_ack and src_update. Ie, there can be 3 scearios:
      // 1. update one cycle before ack
      // 2. ack one cycle before update
      // 3. update / ack on the same cycle
      // During all 3 cases the read data should be correct
      src_q <= dst_qs;
      txn_bits_q <= '0;
    end
  end

  // The current design (tlul_adapter_reg) does not spit out a request if the destination it chooses
  // (decoded from address) is busy. So this creates a situation in the current design where
  // src_req_i and busy can never be high at the same time.
  // While the code above could be coded directly to be expressed as `src_req & !busy`, which makes
  // the intent clearer, it ends up causing coverage holes from the tool's perspective since that
  // condition cannot be met.
  // Thus we add an assertion here to ensure the condition is always satisfied.
  `ASSERT(BusySrcReqChk_A, busy |-> !src_req, clk_src_i, !rst_src_ni)

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

  logic dst_req_from_src;
  logic dst_req;


  // the software transaction is pulse synced across the domain.
  // the prim_reg_cdc_arb module handles conflicts with ongoing hardware updates.
  prim_pulse_sync u_src_to_dst_req (
    .clk_src_i,
    .rst_src_ni,
    .clk_dst_i,
    .rst_dst_ni,
    .src_pulse_i(src_req),
    .dst_pulse_o(dst_req_from_src)
  );

  prim_reg_cdc_arb #(
    .DataWidth(DataWidth),
    .ResetVal(ResetVal),
    .DstWrReq(DstWrReq)
  ) u_arb (
    .clk_src_i,
    .rst_src_ni,
    .clk_dst_i,
    .rst_dst_ni,
    .src_ack_o(src_ack),
    .src_update_o(src_update),
    .dst_req_i(dst_req_from_src),
    .dst_req_o(dst_req),
    .dst_update_i,
    .dst_ds_i,
    .dst_qs_i,
    .dst_qs_o(dst_qs)
  );


  // Each is valid only when destination request pulse is high
  assign {dst_we_o, dst_re_o, dst_regwen_o} = txn_bits_q & {TxnWidth{dst_req}};

  `ASSERT_KNOWN(SrcBusyKnown_A, src_busy_o, clk_src_i, !rst_src_ni)
  `ASSERT_KNOWN(DstReqKnown_A, dst_req, clk_dst_i, !rst_dst_ni)

  // If busy goes high, we must eventually see an ack
  `ifdef FPV_ON
    `ASSERT(HungHandShake_A, $rose(src_req) |-> strong(##[0:$] src_ack), clk_src_i, !rst_src_ni)
    // TODO: #14913 check if we can add additional sim assertions.
  `endif
endmodule // prim_subreg_cdc
