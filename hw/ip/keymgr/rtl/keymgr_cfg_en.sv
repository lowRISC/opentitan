// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager CFGEN
// TBD This should be enhanced in the future to contain a shadow copy

`include "prim_assert.sv"

module keymgr_cfg_en #(
  // controls whether clear has an effect on output value during non-init
  parameter bit NonInitClr = 1'b1
) (
  input clk_i,
  input rst_ni,
  input init_i,
  input en_i,
  input set_i,
  input clr_i,
  output logic out_o
);

  logic out_q;
  logic init_q;

  logic vld_clr;
  logic vld_set;
  logic vld_dis;

  assign vld_clr = init_q && clr_i;
  assign vld_set = init_q && set_i;
  assign vld_dis = init_q && !en_i;

  // the same cycle where clear is asserted should already block future
  // configuration
  logic out_clr;
  assign out_clr = NonInitClr ? clr_i : vld_clr;
  assign out_o = ~out_clr & out_q & en_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      init_q <= '0;
    end else if (init_q && !en_i) begin
      init_q <= '0;
    end else if (init_i && en_i) begin
      init_q <= 1'b1;
    end
  end

  // clearing the configure enable always has higher priority than setting
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_q <= 1'b1;
    end else if (vld_dis) begin
      out_q <= 1'b0;
    end else if (vld_set) begin
      out_q <= 1'b1;
    end else if (out_clr) begin
      out_q <= 1'b0;
    end
  end

endmodule // keymgr_cfg_en
