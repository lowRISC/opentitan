// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A very simple interface that represents RACL error log signals. This uses the "maximum footprint"
// approach, sizing for the maximum plausible number of subscribers
//
// The interface has an associated clock and reset because we expect all devices interacting with
// the interface to share a clock and reset domain.

interface racl_error_log_if (input logic clk_i, input logic rst_ni);

  // 64 error log signals (using the maximum-footprint approach and assuming there are at most 64
  // subscribers)
  top_racl_pkg::racl_error_log_t [63:0] errors;

  // A clocking block that should be used by subscribers (blocks that subscribe to policies from
  // racl_ctrl and report errors back to it)
  clocking subscriber_cb @(posedge clk_i);
    output errors;
  endclocking

  // A clocking block that should be used by racl_ctrl
  clocking ctrl_cb @(posedge clk_i);
    input errors;
  endclocking

  // Wait for num_clks clock edges on ctrl_cb, exiting early on reset
  task automatic wait_ctrl_clks_or_rst(int unsigned num_clks);
    fork begin : isolation_fork
      fork
        repeat (num_clks) @(ctrl_cb);
        wait(!rst_ni);
      join_any
      disable fork;
    end join
  endtask

endinterface
