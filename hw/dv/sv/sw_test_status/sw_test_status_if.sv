// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface sw_test_status_if (
  input clk
);
  import top_pkg::*;
  import sw_test_status_pkg::*;

  // Single cycle qualifier for the sw_test_status_val.
  logic valid;

  // Address to which the test status is written to.
  logic [TL_AW-1:0] sw_test_status_addr;

  // SW test status written by the CPU.
  logic [TL_DW-1:0] sw_test_status_val;

  // SW test status indication.
  sw_test_status_e sw_test_status_d;
  sw_test_status_e sw_test_status = SwTestStatusUnderReset;

  // If the sw_test_status reaches the terminal states, assert that we are done.
  bit sw_test_done;

  assign sw_test_status_d = valid ? sw_test_status_e'(sw_test_status_val[15:0]) : sw_test_status;

  always_ff @(posedge clk) begin
    if (valid) begin
      sw_test_status <= sw_test_status_d;
      sw_test_done <= sw_test_done | (sw_test_status_d inside {SwTestStatusPassed, SwTestStatusFailed});
      $display("%t [%m]: Detected SW test status change: %0s", $time, sw_test_status_d.name);
    end
  end
endinterface
