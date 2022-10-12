// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface entropy_src_xht_if import entropy_src_pkg::*;
(
  input wire clk,
  input wire rst_n
);

  entropy_src_xht_req_t req;
  entropy_src_xht_rsp_t rsp;

  logic entropy_bit_valid_q;

  always @(posedge clk) begin
    entropy_bit_valid_q <= req.entropy_bit_valid;
  end

  clocking xht_cb @(posedge clk);
    input req;
    output rsp;
  endclocking

  clocking mon_cb @(posedge clk);
    input req;
    input rsp;
    input entropy_bit_valid_q;
  endclocking

endinterface
