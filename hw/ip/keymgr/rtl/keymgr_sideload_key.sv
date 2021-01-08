// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager sideload key

`include "prim_assert.sv"

module keymgr_sideload_key import keymgr_pkg::*;(
  input clk_i,
  input rst_ni,
  input en_i,
  input set_en_i,
  input set_i,
  input clr_i,
  input [Shares-1:0][RandWidth-1:0] entropy_i,
  input [Shares-1:0][KeyWidth-1:0] key_i,
  output hw_key_req_t key_o
);

  localparam int EntropyCopies = KeyWidth / 32;

  logic valid_q;
  logic [Shares-1:0][KeyWidth-1:0] key_q;

  assign key_o.valid = valid_q & en_i;
  assign key_o.key_share0 = key_q[0];
  assign key_o.key_share1 = key_q[1];

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q <= 1'b0;
    end else if (!en_i || clr_i) begin
      valid_q <= 1'b0;
    end else if (set_i) begin
      valid_q <= 1'b1;
    end
  end

  always_ff @(posedge clk_i) begin
    if (clr_i) begin
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
