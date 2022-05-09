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

  spi_data_t   jedec_id;
  logic [15:0] device_id;

  // Timeout
  initial begin
    #1ms
    $display("TEST TIMED OUT!!");
    $finish();
  end

  initial begin
    automatic spi_data_t temp_status;
    automatic logic [23:0] temp_jedec_id;
    automatic int unsigned num_cc;
    automatic spi_queue_t  rdata = {};
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

    repeat(10) @(negedge clk);

    // Test: Jedec ID
    // CcNum 7, Cc 'h 7F
    spiflash_readjedec(
      sif.tb,
      spi_device_pkg::CmdJedecId,
      8'h 7F,
      num_cc,
      temp_jedec_id
    );

    jedec_id  = temp_jedec_id[23:16];
    device_id = temp_jedec_id[15:0];
    $display("Received Jedec ID: %2Xh (CC: %2d), Device ID: %4Xh",
      jedec_id, num_cc, device_id);

    repeat(10) @(negedge clk);

    // Read SFDP from SPIFlash (not inside SPI_DEVICE IP)
    spiflash_readsfdp(
      sif.tb,
      spi_device_pkg::CmdReadSfdp, // 5Ah
      24'h 00_0000, // addr
      32,           // size
      rdata
    );

    // clean-up for SFDP
    rdata.delete();

    // Finish
    $finish();
  end

  // TODO: Do Factory to load proper sequence for the test

endprogram : prog_passthrough_host
