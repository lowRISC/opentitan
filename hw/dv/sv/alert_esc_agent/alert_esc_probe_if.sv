// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this is a probing interface for signal "esc_en_i":
// "esc_en_i" is one of the input signal for "prim_esc_sender"
// "esc_en_i" needs to be probed because: in esc_sig_integrity_fail cases, "esc_en_i" gated if next
// state the expected resp_p should be high or not. However, from the esc_receiver interface, we
// can only see "esc_p/n", which follows "esc_en_i" with one clock cycle delay.
// Thus we need to probe this signal to accurately predict the signal integrity fail count.
interface alert_esc_probe_if (
  input clk,
  input rst_n
);

  wire esc_en;

  clocking monitor_cb @(posedge clk);
    input rst_n;
    input esc_en;
  endclocking

  function automatic logic get_esc_en();
    return monitor_cb.esc_en;
  endfunction

  task automatic wait_esc_en();
    while (esc_en !== 1'b1) @(monitor_cb);
  endtask

endinterface
