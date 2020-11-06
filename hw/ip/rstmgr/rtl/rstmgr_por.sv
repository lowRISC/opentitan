// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module stretches the POR
//

`include "prim_assert.sv"

module rstmgr_por #(
  parameter int FilterStages = 3,
  parameter int StretchCount = 32
) (
  input clk_i,
  input rst_ni,
  input scan_rst_ni,
  input scanmode_i,
  output logic rst_no
);
  localparam int CtrWidth = $clog2(StretchCount+1);

  logic rst_root_n;
  logic [FilterStages-1:0] rst_filter_n;
  logic rst_stable;
  logic rst_clean_n;
  logic [CtrWidth-1:0] cnt;
  logic cnt_en;

  // sync the POR
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) rst_sync (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d_i(1'b1),
    .q_o(rst_root_n)
  );

  // filter the POR
  always_ff @(posedge clk_i or negedge rst_root_n) begin
    if (!rst_root_n) begin
      rst_filter_n <= '0;
    end else begin
      rst_filter_n <= {rst_filter_n[0 +: FilterStages-1], 1'b1};
    end
  end

  // The stable is a vote of all filter stages.
  // Only when all the stages agree is the reset considered stable and count allowed.

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_rst_clean_mux (
    .clk0_i(rst_filter_n[FilterStages-1]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(rst_clean_n)
  );

  assign rst_stable = &rst_filter_n;
  assign cnt_en = rst_stable & !rst_no;

  // stretch the POR
  always_ff @(posedge clk_i or negedge rst_clean_n) begin
    if (!rst_clean_n) begin
      cnt <= '0;
      rst_no <= '0;
    end else if (!rst_stable) begin
      cnt <= '0;
      rst_no <= '0;
    end else if (cnt_en && cnt == StretchCount) begin
      rst_no <= 1'b1;
    end else if (cnt_en) begin
      cnt <= cnt + 1'b1;
    end
  end

endmodule // rstmgr_por
