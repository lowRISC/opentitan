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

  spi_data_t mirrored_storage[*]; // Mirrored SPIFlash storage

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
    automatic spi_queue_t  rdata_cmp = {};
    automatic bit pass = 1'b 1;
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

    repeat(10) @(negedge clk);

    // Read commands:
    spiflash_read(
      sif,
      spi_device_pkg::CmdReadData, // 03h
      32'h 0000_0103,              // address
      0,                           // 3B mode
      0,                           // dummy
      256,                         // size
      IoSingle,                    // io_mode
      rdata
    );

    // Update mirrored storage
    update_storage('h 103, 256, rdata);

    repeat(10) @(negedge clk);

    // Issue another command to the partial of the address and compare
    spiflash_read(
      sif,
      spi_device_pkg::CmdReadQuad,
      32'h 0000_103,               // address
      0,                           // 3B mode
      3,                           // dummy
      131,                         // size
      IoQuad,                      // io_mode
      rdata_cmp
    );

    if (!compare_storage('h 103, 131, rdata_cmp)) pass = 1'b 0;

    $display("Read Data size: %3d / %3d", rdata.size(), rdata_cmp.size());
    $display("Read Data (1st): %p", rdata);
    $display("Read Data (2nd): %p", rdata_cmp);

    rdata.delete();
    rdata_cmp.delete();

    repeat(10) @(negedge clk);

    // Finish
    if (pass) begin
      $display("TEST PASSED CHECKS");
    end
    $finish();
  end

  // TODO: Do Factory to load proper sequence for the test


  // Access to Mirrored storage
  function automatic void write_byte(int unsigned addr, spi_data_t data);
    mirrored_storage[addr] = data;
  endfunction : write_byte

  function automatic spi_data_t read_byte(int unsigned addr);
    return mirrored_storage[addr];
  endfunction : read_byte

  function automatic void update_storage(
    int unsigned addr,
    int unsigned size,
    spi_queue_t  data
  );
    for (int unsigned i = 0 ; i < size ; i++) begin
      // If not exist, just update
      write_byte(addr+i, data[i]);
    end
  endfunction : update_storage

  function automatic bit compare_storage(
    int unsigned addr,
    int unsigned size,
    spi_queue_t  data
  );
    automatic bit pass = 1'b 1;
    for (int unsigned i = 0 ; i < size ; i++) begin
      if (!mirrored_storage.exists(addr+i)) write_byte(addr+i, data[i]);
      else if (read_byte(addr+i) != data[i]) begin
        pass = 1'b 0;
      end
    end
    return pass;
  endfunction : compare_storage

endprogram : prog_passthrough_host
