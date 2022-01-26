// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// A one-signal interface for escalation signals

interface otbn_escalate_if (
  input logic clk_i,
  input logic rst_ni
);

  lc_ctrl_pkg::lc_tx_t enable;

  function automatic void reset_signals();
    enable = lc_ctrl_pkg::Off;
  endfunction

  task automatic set_after_n_clocks(int unsigned n);
    `DV_SPINWAIT_EXIT(
      begin
        repeat (n) @(posedge clk_i);
        enable = lc_ctrl_pkg::On;
      end,
      @(negedge rst_ni);,
      "Not setting enable signal because we've gone into reset",
      "otbn_escalate_if")
  endtask

endinterface
