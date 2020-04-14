// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface sw_test_status_if ();
  import top_pkg::*;
  import sw_test_status_pkg::*;

  // Single cycle qualifier for the sw_test_status_val.
  logic valid;

  // Address to which the test status is written to.
  logic [TL_AW-1:0] sw_test_status_addr;

  // SW test status written by the CPU.
  logic [TL_DW-1:0] sw_test_status_val;

  // SW test status indication.
  sw_test_status_e sw_test_status;

  // If the sw_test_status reaches the terminal states, assert that we are done.
  bit sw_test_done;

  // Logic that updates the sw_test_status from the val.
  // Note that sw_test_status is set by the testbench when the CPU is under reset.
  initial begin
    forever begin
      @(valid);
      if (valid) begin
        sw_test_status = sw_test_status_e'(sw_test_status_val[15:0]);
        if (!sw_test_done) begin
          sw_test_done = (sw_test_status inside {SwTestStatusPassed, SwTestStatusFailed});
        end
      end
    end
  end

endinterface
