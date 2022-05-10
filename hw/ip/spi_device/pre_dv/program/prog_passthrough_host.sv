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

  import spi_device_pkg::Addr3B, spi_device_pkg::Addr4B,
         spi_device_pkg::addr_mode_e;
  addr_mode_e addr_mode;

  // FIXME: Make it configurable by ReadSfdp
  parameter int unsigned FlashSize = 1024*1024;

  import spi_device_pkg::CmdReadStatus1,
         spi_device_pkg::CmdJedecId,
         spi_device_pkg::CmdPageProgram,
         spi_device_pkg::CmdSectorErase,
         spi_device_pkg::CmdBlockErase32,
         spi_device_pkg::CmdBlockErase64,
         spi_device_pkg::CmdReadData,
         spi_device_pkg::CmdReadFast,
         spi_device_pkg::CmdReadDual,
         spi_device_pkg::CmdReadQuad,
         spi_device_pkg::CmdWriteDisable,
         spi_device_pkg::CmdWriteEnable,
         spi_device_pkg::CmdEn4B,
         spi_device_pkg::CmdEx4B,
         spi_device_pkg::CmdReadSfdp,
         spi_device_pkg::CmdResetDevice;

  // Timeout
  initial begin
    #1ms
    $display("TEST TIMED OUT!!");
    $finish();
  end

  initial begin
    automatic spi_data_t   temp_status;
    automatic logic [23:0] temp_jedec_id;
    automatic int unsigned num_cc;
    automatic spi_queue_t  rdata = {};
    automatic spi_queue_t  rdata_cmp = {};

    automatic bit pass = 1'b 1;
    automatic bit subtask_pass;
    // Default value
    sif.csb = 1'b 1;
    addr_mode = Addr3B; // default 3B mode

    @(posedge rst_n);

    // SW initialization tool 2.8us incl. DPSRAM zerorize.
    #2us

    @(negedge clk);
    // Test: Issue Status Read command without intercept
    spiflash_readstatus(
      sif.tb,
      CmdReadStatus1,
      temp_status
    );

    $display("Received Status: %2Xh", temp_status);
    status[0] = temp_status;

    repeat(10) @(negedge clk);

    // Test: Jedec ID
    // CcNum 7, Cc 'h 7F
    spiflash_readjedec(
      sif.tb,
      CmdJedecId,
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
      CmdReadSfdp, // 5Ah
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
      CmdReadData, // 03h
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
      CmdReadQuad,
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

    // Test EN4B
    test_addr_4b(subtask_pass);
    if (subtask_pass == 1'b 0) pass = 1'b 0;

    wait_trans();

    // Finish
    if (pass) begin
      $display("TEST PASSED CHECKS");
    end

    $finish();

  end

  static task automatic wait_trans();
    repeat(10) @(negedge clk);
  endtask : wait_trans

  static task test_addr_4b(bit pass);
    automatic spi_queue_t rdata;
    automatic logic [31:0] address;
    automatic int unsigned size;

    SpiTransRead trans = new();
    // Random address and size
    trans.randomize() with {
      size < 32;
      address < FlashSize - size;
      addr_mode == 0; // 3B only
    };
    trans.display();

    if (addr_mode != Addr3B) begin
      spiflash_addr_4b(sif.tb, CmdEx4B);

      addr_mode = Addr3B;

      wait_trans();
    end

    // FIXME: Call SPI Driver
    spiflash_read(
      sif.tb,
      trans.cmd,
      trans.address,
      trans.addr_mode,
      trans.dummy,
      trans.size,
      trans.io_mode,
      rdata
    );

    update_storage(trans.address, trans.size, rdata);
    rdata.delete();

    wait_trans();

    address = trans.address;
    size    = trans.size;

    trans = new();

    trans.randomize() with {
      size      == local::size;
      address   == local::address;
      addr_mode == 1; // Addr 4B
    };
    trans.display();

    // Issue En4B
    spiflash_addr_4b(sif.tb, CmdEn4B);

    addr_mode = Addr4B;

    wait_trans();

    $display("Issuing 4B address command");

    spiflash_read(
      sif.tb,
      trans.cmd,
      trans.address,
      trans.addr_mode,
      trans.dummy,
      trans.size,
      trans.io_mode,
      rdata
    );

    wait_trans();

    if (!compare_storage(trans.address, trans.size, rdata)) pass = 1'b 0;
    else pass = 1'b 1;

    rdata.delete();

  endtask : test_addr_4b

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
