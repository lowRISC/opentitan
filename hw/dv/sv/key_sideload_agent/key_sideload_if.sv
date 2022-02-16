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

  task automatic wait_clks(int rsp_delay);
    for (int i = 0; i < rsp_delay; i++) begin
      if (!rst_ni) break;
      @(posedge clk_i or negedge rst_ni);
    end
  endtask
endinterface
