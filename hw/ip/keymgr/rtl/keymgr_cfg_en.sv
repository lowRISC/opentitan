// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager CFGEN
// TBD This should be enhanced in the future to contain a shadow copy

`include "prim_assert.sv"

module keymgr_cfg_en (
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

  // the same cycle where clear is asserted should already block future
  // configuration
  assign out_o = ~clr_i & out_q & en_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      init_q <= '0;
    end else if (init_q && !en_i) begin
      init_q <= '0;
    end else if (init_i) begin
      init_q <= 1'b1;
    end
  end

  // clearing the configure enable always has higher priority than setting
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_q <= 1'b1;
    end else if (init_q && !en_i) begin
      out_q <= 1'b0;
    end else if (init_q && set_i) begin
      out_q <= 1'b1;
    end else if (init_q && clr_i) begin
      out_q <= 1'b0;
    end
  end

endmodule // keymgr_cfg_en
