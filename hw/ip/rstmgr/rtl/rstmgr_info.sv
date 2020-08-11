// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module records the reset reason
//

`include "prim_assert.sv"

module rstmgr_info #(
    parameter int Reasons = 4
) (
    input                      clk_i,
    input                      rst_ni,
    input                      rst_cpu_ni,
    input        [Reasons-1:0] rst_req_i,
    input                      wr_i,
    input        [  Reasons:0] data_i,  // inclusive of POR
    output logic [  Reasons:0] rst_reasons_o  // inclusive of POR
);

  logic [Reasons-1:0] reasons;
  logic por;
  logic first_reset;
  logic rst_cpu_nq;

  prim_flop_2sync #(
      .Width(1),
      .ResetValue('0)
  ) u_cpu_reset_synced (
      .clk_i (clk_i),
      .rst_ni(rst_ni),
      .d_i   (rst_cpu_ni),
      .q_o   (rst_cpu_nq)
  );

  // first reset is a flag that blocks reset recording until first de-assertion
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      first_reset <= 1'b1;
    end else if (rst_cpu_nq) begin
      first_reset <= 1'b0;
    end
  end

  // if cpu has gone into reset, record reset causes
  // the reasons is a logical OR, so that signals that were once asserted do not go away.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      por <= 1'b1;
      reasons <= '0;
    end else if (!rst_cpu_nq && !first_reset) begin
      reasons <= reasons | rst_req_i;
    end else if (wr_i) begin
      {reasons, por} <= {reasons, por} & ~data_i;
    end
  end

  assign rst_reasons_o = {reasons, por};

endmodule  // rstmgr_info
