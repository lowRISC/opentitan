// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface sw_test_status_if #(
  parameter int AddrWidth = 32
) (
  input logic clk_i,
  input logic wr_valid,             // Qualified write access.
  input logic [AddrWidth-1:0] addr, // Incoming addr.
  input logic [15:0] data           // Incoming data.
);

`ifdef UVM
  import uvm_pkg::*;
`endif
  import sw_test_status_pkg::*;

  // macro includes
  `include "dv_macros.svh"

  // Address to which the test status is written to. This is set by the testbench.
  logic [AddrWidth-1:0] sw_test_status_addr;

  // Validate the incoming write address.
  logic data_valid;
  assign data_valid = wr_valid && (addr == sw_test_status_addr);

  // SW test status indication.
  sw_test_status_e sw_test_status = SwTestStatusUnderReset;

  // If the sw_test_status reaches the terminal states, assert that we are done.
  bit sw_test_done;
  bit sw_test_passed;

  always @(posedge clk_i) begin
    if (data_valid) begin
      sw_test_status = sw_test_status_e'(data);
      sw_test_done = sw_test_done | sw_test_status inside {SwTestStatusPassed, SwTestStatusFailed};
      sw_test_passed = sw_test_status == SwTestStatusPassed;
      if (sw_test_status == SwTestStatusPassed) begin
        `dv_info("==== SW TEST PASSED ====")
      end else if (sw_test_status == SwTestStatusFailed) begin
        `dv_error("==== SW TEST FAILED ====")
      end else begin
        `dv_info($sformatf("SW test status changed: %0s", sw_test_status.name()))
      end
    end
  end

endinterface
