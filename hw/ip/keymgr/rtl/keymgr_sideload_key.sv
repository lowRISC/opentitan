// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager sideload key

`include "prim_assert.sv"

module keymgr_sideload_key import keymgr_pkg::*; #(
  parameter int Width = KeyWidth
) (
  input clk_i,
  input rst_ni,
  input en_i,
  input set_en_i,
  input set_i,
  input clr_i,
  input [Shares-1:0][RandWidth-1:0] entropy_i,
  input [Shares-1:0][Width-1:0] key_i,
  output logic valid_o,
  output logic [Shares-1:0][Width-1:0] key_o
);

  localparam int EntropyCopies = Width / RandWidth;

  logic valid_q;
  logic [Shares-1:0][Width-1:0] key_q;

  assign valid_o = valid_q & en_i;
  assign key_o = key_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q <= 1'b0;
    end else if (!en_i || clr_i) begin
      valid_q <= 1'b0;
    end else if (set_i) begin
      valid_q <= 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      key_q <= '0;
    end else if (clr_i) begin
      for (int i = 0; i < Shares; i++) begin
        key_q[i] <= {EntropyCopies{entropy_i[i]}};
      end
    end else if (set_i) begin
      for (int i = 0; i < Shares; i++) begin
        key_q[i] <= set_en_i ? key_i[i] : {EntropyCopies{entropy_i[i]}};
      end
    end
  end

endmodule // keymgr_sideload_key
