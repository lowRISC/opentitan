// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface pwrmgr_clk_ctrl_if (
  input logic clk,
  input logic rst_n,
  input logic clk_slow,
  input logic rst_slow_n
);
  import uvm_pkg::*;
  import pwrmgr_pkg::*;


  // interface pins
  pwrmgr_pkg::pwr_ast_req_t pwr_ast_req;
  pwrmgr_pkg::pwr_clk_req_t pwr_clk_req;

  clocking cb @(posedge clk);
  endclocking // cb

  clocking scb @(posedge clk_slow);
  endclocking // scb

  // wait for rst_n to assert and then deassert
  task automatic wait_for_reset(bit wait_negedge = 1'b1, bit wait_posedge = 1'b1);
    if (wait_negedge && ($isunknown(rst_n) || rst_n === 1'b1)) @(negedge rst_n);
    if (wait_posedge && (rst_n === 1'b0)) @(posedge rst_n);
  endtask

endinterface
