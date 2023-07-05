// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// An interface for lifecycle controller related ports

interface otbn_escalate_if (
  input logic clk_i,
  input logic rst_ni
);

  lc_ctrl_pkg::lc_tx_t enable;
  lc_ctrl_pkg::lc_tx_t req;
  lc_ctrl_pkg::lc_tx_t ack;

  task automatic reset_signals();
    enable <= lc_ctrl_pkg::Off;
    req <= lc_ctrl_pkg::Off;
  endtask

  task automatic randomize_rma_req_after_n_clocks(int unsigned n, int t_weight = 2,
                                                  int f_weight = 2, int other_weight = 1);
    // Send Req
    `DV_SPINWAIT_EXIT(begin
        repeat (n) @(posedge clk_i);
        req <= cip_base_pkg::get_rand_lc_tx_val(.t_weight(t_weight),
                                                .f_weight(f_weight),
                                                .other_weight(other_weight));
      end, @(negedge rst_ni);, "Not setting req signal because we've gone into reset",
                      "otbn_escalate_if")
  endtask

  task automatic randomize_enable_after_n_clocks(int unsigned n, int t_weight = 2, int f_weight = 2,
                                                 int other_weight = 1);
    `DV_SPINWAIT_EXIT(begin
        repeat (n) @(posedge clk_i);
          enable <= cip_base_pkg::get_rand_lc_tx_val(.t_weight(t_weight),
                                                     .f_weight(f_weight),
                                                     .other_weight(other_weight));
      end, @(negedge rst_ni);, "Not setting enable signal because we've gone into reset",
                      "otbn_escalate_if")
  endtask


endinterface
