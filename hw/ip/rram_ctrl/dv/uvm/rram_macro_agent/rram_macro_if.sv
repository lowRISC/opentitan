// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Interface that tracks request / response handshake between rram_ctrl and rram_macro

`include "prim_assert.sv"

interface rram_macro_if (
  input wire clk_i,
  input wire rst_ni
);
  import rram_ctrl_pkg::rram_macro_req_t;
  import rram_ctrl_pkg::rram_macro_rsp_t;

  default clocking @(posedge clk_i); endclocking
  default disable iff (!rst_ni);

  // The core interface signals.
  wire rram_macro_req_t req;
  wire rram_macro_rsp_t rsp;

  clocking mon_cb @(posedge clk_i);
    input req;
    input rsp;
  endclocking
endinterface
