// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module generates the leaf resets and instantiates the associated reset
// checks.

`include "prim_assert.sv"

module rstmgr_leaf_rst
  import rstmgr_pkg::*;
  import rstmgr_reg_pkg::*;
  import prim_mubi_pkg::mubi4_t; #(
  parameter bit SecCheck = 1
) (
  input clk_i,
  input rst_ni,
  input leaf_clk_i,
  input parent_rst_ni,
  input sw_rst_req_ni,
  input scan_rst_ni,
  input scan_sel,
  output mubi4_t rst_en_o,
  output logic leaf_rst_o,
  output logic err_o,
  output logic fsm_err_o
);

  logic leaf_rst_sync;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_rst_sync (
    .clk_i(leaf_clk_i),
    .rst_ni(parent_rst_ni),
    .d_i(sw_rst_req_ni),
    .q_o(leaf_rst_sync)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_rst_mux (
    .clk0_i(leaf_rst_sync),
    .clk1_i(scan_rst_ni),
    .sel_i(scan_sel),
    .clk_o(leaf_rst_o)
  );

  // once software requests a reset, hold on to the request until the consistency
  // checker passes the assertion check point
  logic sw_rst_req_q;
  logic clr_sw_rst_req;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
       sw_rst_req_q <= '0;
    end else if (sw_rst_req_q && clr_sw_rst_req) begin
       sw_rst_req_q <= '0;
    end else if (!sw_rst_req_q && !sw_rst_req_ni && !clr_sw_rst_req) begin
       sw_rst_req_q <= 1'b1;
    end
  end

  if (SecCheck) begin : gen_rst_chk
    // SEC_CM: LEAF.RST.BKGN_CHK
    rstmgr_cnsty_chk u_rst_chk (
      .clk_i,
      .rst_ni,
      .child_clk_i(leaf_clk_i),
      .child_rst_ni(leaf_rst_o),
      .parent_rst_ni,
      .sw_rst_req_i(sw_rst_req_q | ~sw_rst_req_ni),
      .sw_rst_req_clr_o(clr_sw_rst_req),
      .err_o,
      .fsm_err_o
    );
  end else begin : gen_no_rst_chk
    logic unused_sig;
    assign unused_sig = sw_rst_req_q | clr_sw_rst_req;

    assign err_o = '0;
    assign fsm_err_o = '0;
  end

  // reset asserted indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(prim_mubi_pkg::MuBi4True)
  ) u_prim_mubi4_sender (
    .clk_i(leaf_clk_i),
    .rst_ni(leaf_rst_o),
    .mubi_i(prim_mubi_pkg::MuBi4False),
    .mubi_o(rst_en_o)
  );

endmodule // rstmgr_leaf_rst
