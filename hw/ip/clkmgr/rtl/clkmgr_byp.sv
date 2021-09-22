// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Handle clock manager bypass requests

module clkmgr_byp import clkmgr_pkg::*; import lc_ctrl_pkg::lc_tx_t; # (
  parameter int NumDivClks = 1
) (
  input                   clk_i,
  input                   rst_ni,
  input  lc_tx_t          en_i,
  input  lc_tx_t          byp_req,
  output lc_tx_t          ast_clk_byp_req_o,
  input  lc_tx_t          ast_clk_byp_ack_i,
  input  lc_tx_t          lc_clk_byp_req_i,
  output lc_tx_t          lc_clk_byp_ack_o,
  input  [NumDivClks-1:0] step_down_acks_i,
  output lc_tx_t          step_down_req_o
);

  lc_tx_t reg_clk_byp_req;
  lc_tx_t on_val;
  assign on_val = lc_ctrl_pkg::On;

  // Generate qualified reg clk bypass request
  for (genvar i = 0; i < $bits(lc_tx_t); i++) begin : gen_clk_byp
    prim_buf u_buf (
      .in_i(on_val[i] ? byp_req[i] & en_i[i] : byp_req[i] | en_i[i]),
      .out_o(reg_clk_byp_req[i])
    );
  end

  lc_tx_t ast_clk_byp_req;
  always_comb begin
    ast_clk_byp_req = lc_ctrl_pkg::Off;
    if (lc_clk_byp_req_i == lc_ctrl_pkg::On) begin
      ast_clk_byp_req = lc_ctrl_pkg::On;
    end else if (reg_clk_byp_req == lc_ctrl_pkg::On) begin
      ast_clk_byp_req = lc_ctrl_pkg::On;
    end
  end

  prim_lc_sender u_clk_byp_req (
   .clk_i,
   .rst_ni,
   .lc_en_i(ast_clk_byp_req),
   .lc_en_o(ast_clk_byp_req_o)
  );

  prim_lc_sync u_rcv (
    .clk_i,
    .rst_ni,
    .lc_en_i(ast_clk_byp_ack_i),
    .lc_en_o(step_down_req_o)
  );

  // only ack the lc_ctrl if it made a request.
  prim_lc_sender u_send (
   .clk_i,
   .rst_ni,
   .lc_en_i((&step_down_acks_i) ? lc_clk_byp_req_i : lc_ctrl_pkg::Off),
   .lc_en_o(lc_clk_byp_ack_o)
  );


endmodule // clkmgr_byp
