// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface entropy_src_xht_if import entropy_src_pkg::*;
(
  input wire clk,
  input wire rst_n
);
  localparam int RngBusWidth = 4;
  localparam int RngBusBitSelWidth = prim_util_pkg::vbits(RngBusWidth);

  logic                         entropy_bit_valid;
  logic [RngBusWidth-1:0]       entropy_bit;
  logic [RngBusBitSelWidth-1:0] entropy_bit_sel;

  entropy_src_xht_req_t req;
  entropy_src_xht_rsp_t rsp;

  logic entropy_bit_valid_q;

  always @(posedge clk) begin
    entropy_bit_valid_q <= entropy_bit_valid;
  end

  clocking xht_cb @(posedge clk);
    input req;
    output rsp;
  endclocking

  clocking mon_cb @(posedge clk);
    input req;
    input rsp;
    input entropy_bit_valid;
    input entropy_bit;
    input entropy_bit_sel;
    input entropy_bit_valid_q;
  endclocking

endinterface
