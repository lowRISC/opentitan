// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

program prog_passthrough_host
  import spid_common::*;
(
  input logic clk,
  input logic rst_n,

  spi_if sif
);

  // Tracked Flash variables
  spi_data_t [2:0] status;
  // Timeout
  initial begin
    #1ms
    $display("TEST TIMED OUT!!");
    $finish();
  end

  initial begin
    automatic spi_data_t temp_status;
    // Default value
    sif.csb = 1'b 1;

    @(posedge rst_n);

    // SW initialization tool 2.8us incl. DPSRAM zerorize.
    #2us

    @(negedge clk);
    // Test: Issue Status Read command without intercept
    spiflash_readstatus(
      sif.tb,
      spi_device_pkg::CmdReadStatus1,
      temp_status
    );

    $display("Received Status: %2Xh", temp_status);
    status[0] = temp_status;

    forever begin
      @(posedge clk);
    end
  end

  // TODO: Do Factory to load proper sequence for the test

endprogram : prog_passthrough_host
