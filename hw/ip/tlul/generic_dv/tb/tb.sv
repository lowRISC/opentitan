// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tb;

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import xbar_test_pkg::*;


  wire clk, rst_n;
  // reference clock for scb/seq and this clock isn't connected to any design clock
  // TODO, reset is the combined all the resets. Re-visit this if partial reset is needed
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));

  // this file is auto-generated and the path to this file should be provided in xbar_*_sim.core
  `include "tb__xbar_connect.sv"

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env*", "clk_rst_vif", clk_rst_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
