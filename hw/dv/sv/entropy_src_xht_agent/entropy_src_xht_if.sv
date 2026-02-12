// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface entropy_src_xht_if import entropy_src_pkg::*;
(
  input wire clk,
  input wire rst_n
);
  localparam int RngBusWidth = `RNG_BUS_WIDTH;
  localparam int RngBusBitSelWidth = prim_util_pkg::vbits(RngBusWidth);

  logic                            entropy_valid;
  logic [RngBusWidth-1:0]          entropy_bits;
  logic [RngBusBitSelWidth-1:0]    entropy_bit_sel;
  logic [16+RngBusBitSelWidth-1:0] health_test_window;

  entropy_src_xht_meta_req_t req;
  entropy_src_xht_meta_rsp_t rsp;

  logic entropy_valid_q;

  always @(posedge clk) begin
    entropy_valid_q <= entropy_valid;
  end

  clocking xht_cb @(posedge clk);
    input req;
    output rsp;
  endclocking

  clocking mon_cb @(posedge clk);
    input req;
    input rsp;
    input entropy_valid;
    input entropy_bits;
    input entropy_bit_sel;
    input health_test_window;
    input entropy_valid_q;
  endclocking

endinterface
