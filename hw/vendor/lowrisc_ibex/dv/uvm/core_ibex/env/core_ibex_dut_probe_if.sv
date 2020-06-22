// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to probe DUT internal signal
interface core_ibex_dut_probe_if(input logic clk);
  logic                 reset;
  logic                 illegal_instr;
  logic                 ecall;
  logic                 wfi;
  logic                 ebreak;
  logic                 dret;
  logic                 mret;
  logic                 fetch_enable;
  logic                 core_sleep;
  logic                 debug_req;
  ibex_pkg::priv_lvl_e  priv_mode;

  clocking dut_cb @(posedge clk);
    output fetch_enable;
    output debug_req;
    input reset;
    input illegal_instr;
    input ecall;
    input wfi;
    input ebreak;
    input dret;
    input mret;
    input core_sleep;
    input priv_mode;
  endclocking

  initial begin
    debug_req = 1'b0;
  end

endinterface
