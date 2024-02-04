// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Wrapper module for computing enable / disable status on family of clocks

module clkmgr_clk_status #(
  parameter int NumClocks = 1,
  parameter int FilterStages = 2
) (
  input clk_i,
  input rst_ni,
  input [NumClocks-1:0] ens_i,
  output logic status_o
);

  // The enables are coming from different clock domains,
  // therefore after synchronization we must de-bounce the
  // signal to ensure it is stable
  logic [NumClocks-1:0] ens_sync;
  prim_flop_2sync #(
    .Width(NumClocks)
  ) u_en_sync (
    .clk_i,
    .rst_ni,
    .d_i(ens_i),
    .q_o(ens_sync)
  );

  logic [FilterStages-1:0] en_q, dis_q, en_d, dis_d;

  // enable is true when all inputs are 1
  assign en_d = {en_q[FilterStages-2:0], &ens_sync};

  // disable is true all all inputs are 0
  assign dis_d = {dis_q[FilterStages-2:0], ~|ens_sync};

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      en_q <= '0;
      dis_q <= '0;
    end else begin
      en_q <= en_d;
      dis_q <= dis_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      status_o <= '0;
    end else if (&en_q) begin
      status_o <= 1'b1;
    end else if (&dis_q) begin
      status_o <= 1'b0;
    end
  end

endmodule // clkmgr_clk_status
