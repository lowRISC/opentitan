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
  input pok_i, // TODO: This should not be an actual separate port but the POR itself
               // However, this cannot be done until AST integration is done.
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
    .ResetValue(0)
  ) rst_sync (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d(1'b1),
    .q(rst_root_n)
  );

  // filter the POR
  always_ff @(posedge clk_i or negedge rst_root_n) begin
    if (!rst_root_n) begin
      rst_filter_n <= '0;
    end else if (pok_i) begin // once AST is in, this conditional should not be here.
      rst_filter_n <= {rst_filter_n[0 +: FilterStages-1], 1'b1};
    end
  end

  // The stable is a vote of all filter stages.
  // Only when all the stages agree is the reset considered stable and count allowed.
  assign rst_clean_n = rst_filter_n[FilterStages-1];
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
