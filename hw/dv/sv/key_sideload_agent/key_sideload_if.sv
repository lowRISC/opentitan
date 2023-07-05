// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface key_sideload_if #(
  parameter type KEY_T = keymgr_pkg::hw_key_req_t
) (
  input logic clk_i,
  input logic rst_ni,
  // This struct contains three fields:
  // - valid
  // - key_share0
  // - key_share1
  output KEY_T sideload_key
);

  string msg_id = "key_sideload_if";

  task automatic wait_valid(logic is_valid);
    wait (sideload_key.valid === is_valid);
  endtask

  // The following functions are basically copied over from clk_rst_if.sv as we don't have access
  // to the clock and reset interface.

  // Wait for 'num_clks' clocks based on the positive clock edge.
  task automatic wait_clks(int num_clks);
    repeat (num_clks) @(posedge clk_i);
  endtask

  // Wait for rst_ni to assert and then deassert or just either of the two.
  task automatic wait_for_reset(bit wait_negedge = 1'b1, bit wait_posedge = 1'b1);
    if (wait_negedge && ($isunknown(rst_ni) || rst_ni === 1'b1)) @(negedge rst_ni);
    if (wait_posedge && (rst_ni === 1'b0)) @(posedge rst_ni);
  endtask

  // Wait for 'num_clks' clocks based on the positive clock edge or reset, whichever comes first.
  task automatic wait_clks_or_rst(int num_clks);
    fork
      wait_clks(num_clks);
      wait_for_reset(.wait_negedge(1'b1), .wait_posedge(1'b0));
    join_any
  endtask
endinterface
