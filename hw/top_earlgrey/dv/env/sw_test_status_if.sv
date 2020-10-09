// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface sw_test_status_if (
  input clk,
  input valid,
  input bit [15:0] data
);

  import bus_params_pkg::*;
  import sw_test_status_pkg::*;
`ifdef UVM
  import uvm_pkg::*;
  `include "uvm_macros.svh"
`endif

  // Single cycle qualifier for the sw_test_status_val.
  logic valid;

  // Address to which the test status is written to.
  logic [bus_params_pkg::BUS_AW-1:0] sw_test_status_addr;

  // SW test status indication.
  sw_test_status_e sw_test_status;

  // If the sw_test_status reaches the terminal states, assert that we are done.
  bit sw_test_done;

  always @(posedge clk) begin
    if (valid) begin
      if ($cast(sw_test_status, data)) begin
`ifdef UVM
        `uvm_info($sformatf("%m"), $sformatf("Detected SW test status change: %0s",
                                             sw_test_status.name()), UVM_LOW)
`elsif VERILATOR
        $display("%t [%m]: Detected SW test status change: 0x%0h", $time, sw_test_status);
`else
        $display("%t [%m]: Detected SW test status change: %0s", $time, sw_test_status.name());
`endif
        sw_test_done = sw_test_done | (sw_test_status inside {SwTestStatusPassed,
                                                              SwTestStatusFailed});
      end else begin
        $error("%t [%m] Illegal sw_test_status data 0x%0h written to addr 0x%0h",
               $time, data, sw_test_status_addr);
      end
    end
  end

endinterface
