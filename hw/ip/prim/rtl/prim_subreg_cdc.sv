// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Component handling register CDC

`include "prim_assert.sv"

module prim_subreg_cdc #(
  parameter int            DW       = 32,
  parameter logic [DW-1:0] RESVAL   = '0    // Reset value
) (
  input clk_src_i,
  input rst_src_ni,
  input clk_dst_i,
  input rst_dst_ni,

  input src_update_i,
  input src_req_i,
  input [DW-1:0] src_data_i,
  output logic src_busy_o,
  output logic [DW-1:0] src_data_o,

  input [DW-1:0] dst_data_i,
  output logic dst_req_o,
  output logic [DW-1:0] dst_data_o
);

  ////////////////////////////
  // Source domain
  ////////////////////////////
  logic src_ack;
  logic src_busy_q;
  logic [DW-1:0] src_q;

  // busy indication back-pressures upstream if the register is accessed
  // again.  The busy indication is also used as a "commit" indication for
  // resolving software and hardware write conflicts
  always_ff @(posedge clk_src_i or negedge rst_src_ni) begin
    if (!rst_src_ni) begin
      src_busy_q <= '0;
    end else if (src_req_i) begin
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
      src_q <= RESVAL;
    end else if (src_req_i && !busy) begin
      src_q <= src_data_i;
    end else if (src_busy_q && src_ack || src_update_i && !busy) begin
      // sample data whenever a busy transaction finishes OR
      // when an update pulse is seen.
      // TODO: We should add a cover group to test different sync timings
      // between src_ack and src_update. Ie, there can be 3 scearios:
      // 1. update one cycle before ack
      // 2. ack one cycle before update
      // 3. update / ack on the same cycle
      // During all 3 cases the read data should be correct
      src_q <= dst_data_i;
    end
  end

  // src_q is always updated in the clk_src domain.
  // when performing an update to the destination domain, it is guaranteed
  // to not change by protocol.
  assign src_data_o = src_q;
  assign dst_data_o = src_q;

  ////////////////////////////
  // CDC handling
  ////////////////////////////
  prim_sync_reqack u_prim_sync (
    .clk_src_i,
    .rst_src_ni,
    .clk_dst_i,
    .rst_dst_ni,
    .req_chk_i(1'b0),
    // prim_sync_reqack does not natively handle single
    // pulse requests, so use src_busy to even it out.
    .src_req_i(src_req_i | src_busy_q),
    .src_ack_o(src_ack),
    .dst_req_o(dst_req_o),
    // immediately ack on destination once request is seen
    .dst_ack_i(dst_req_o)
  );

  `ASSERT_KNOWN(SrcBusyKnown_A, src_busy_o, clk_src_i, !rst_src_ni)
  `ASSERT_KNOWN(DstReqKnown_A, dst_req_o, clk_dst_i, !rst_dst_ni)

  // If busy goes high, we must eventually see an ack
  `ASSERT(HungHandShake_A, $rose(src_busy_o) |-> strong(##[0:$] src_ack), clk_src_i, !rst_src_ni)

  `ifdef SIMULATION
    logic async_flag;
    always_ff @(posedge src_req_i or posedge dst_req_o or
      negedge rst_src_ni or negedge rst_dst_ni) begin
      if (!rst_src_ni && !rst_dst_ni) begin
        async_flag <= '0;
      end else if (src_req_i) begin
        async_flag <= 1'b1;
      end else if (dst_req_o) begin
        async_flag <= 1'b0;
      end
    end
    `ASSERT(ReqTimeout_A, $rose(async_flag) |-> strong(##[0:3] dst_req_o), clk_dst_i, !rst_dst_ni)
  `endif


endmodule // prim_subreg_cdc
