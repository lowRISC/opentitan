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

  // FIXME: Make it configurable (How?)
  parameter logic [31:0] MailboxAddr = 32'h 00CD_E000;
  parameter int unsigned MailboxSize = 'h 400; // 1kB

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
    automatic string testname;
    automatic bit pass = 1'b 1;
    automatic bit subtask_pass;

    // Default value
    sif.csb = 1'b 1;
    addr_mode = Addr3B; // default 3B mode

    @(posedge rst_n);

    // SW initialization tool 2.8us incl. DPSRAM zerorize.
    #2us

    @(negedge clk);

    $value$plusargs("TESTNAME=%s", testname);

    case (testname)
      "readbasic": begin
        test_readbasic(subtask_pass);
      end

      "addr_4b": begin
        // Test EN4B
        test_addr_4b(subtask_pass);
      end

      "wel": begin
        test_wel(subtask_pass);
      end

      "program": begin
        test_program(subtask_pass);
      end

      default: begin
        $display("Passthrough test requires '+TESTNAME=%%s'");
      end

    endcase

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

  task automatic read_status();
    automatic spi_data_t   temp_status;
    // Test: Issue Status Read command without intercept
    spiflash_readstatus(
      sif.tb,
      CmdReadStatus1,
      temp_status
    );

    $display("Received Status: %2Xh", temp_status);
    status[0] = temp_status;

    wait_trans();

  endtask : read_status

  static task test_readbasic(output bit pass);
    automatic logic [23:0] temp_jedec_id;
    automatic int unsigned num_cc;
    automatic spi_queue_t  rdata = {};
    automatic spi_queue_t  rdata_cmp = {};

    read_status();

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

    wait_trans();

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

    wait_trans();

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

    wait_trans();

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
    else pass = 1'b 1;

    $display("Read Data size: %3d / %3d", rdata.size(), rdata_cmp.size());
    $display("Read Data (1st): %p", rdata);
    $display("Read Data (2nd): %p", rdata_cmp);

    rdata.delete();
    rdata_cmp.delete();

    wait_trans();

  endtask : test_readbasic

  static task test_addr_4b(output bit pass);
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

  static task test_wel(output bit pass);
    automatic bit status_wel;
    automatic bit exp_wel = 1'b 0;
    // This test issues WREN/ WRDI to SPIFlash and check if the SPI_DEVICE IP
    // (not SPIFlash) sets/ clears the STATUS.WEL correctly.
    SpiTrans trans;

    pass = 1'b 1;
    repeat(10) begin
      // Sequence: Random wel set/clear and read status to check
      read_status();

      // Check WEL.
      status_wel = status[0][1];

      if (status_wel != exp_wel) begin
        // FIXME: move to scoreboard
        $display("STATUS.WEL mismatch: EXP(%1b) / RCV(%1b)",
          exp_wel, status_wel);
        pass = 1'b 0;
      end

      trans = new();

      trans.randomize() with {
        cmd inside {
          CmdWriteDisable,
          CmdWriteEnable
        };
        size      == 0;
        address   == '0;
        addr_mode == 0;
      };

      // TODO: Add to TLM FIFO to sequencer then sequencer to Driver

      spiflash_oponly(
        sif.tb,
        trans.cmd
      );

      wait_trans();
      exp_wel = (trans.cmd == CmdWriteEnable) ? 1'b 1: 1'b 0;
    end

  endtask : test_wel

  static task test_program(output bit pass);

    // Test sequence:
    // Issue commands w/ random WEL
    // It is expected for SW to catch program and upload to Mailbox buffer.
    // Read from SPIFlash and from Mailbox buffer then compare
    SpiTransWel     trans_wel; // If WEL is set or not
    SpiTransProgram trans_prog; // Program command to Issue to SPIFlash
    SpiTransRead    trans_read; // To issue read
    int unsigned trans_size;

    int unsigned test_count;

    automatic spi_queue_t rdata_mbx, rdata_spiflash;

    // Decide how many times it repeats
    test_count = $urandom_range(10, 1);

    repeat (test_count) begin
      automatic bit wel = 1'b 0;
      automatic bit busy = 1'b 0;
      // Read Status
      read_status();
      wel = status[0][1];

      // WEL cmd
      trans_wel = new();
      trans_wel.randomize();

      // If flip, issue cmd
      if (((trans_wel.cmd == CmdWriteEnable) && !wel)
        || ((trans_wel.cmd == CmdWriteDisable) && wel)) begin
        trans_wel.display();
        spiflash_oponly(sif.tb, trans_wel.cmd);

        wel = (trans_wel.cmd == CmdWriteEnable) ? 1'b 1 : 1'b 0;
      end

      // Issue page program
      trans_prog = new();
      trans_prog.randomize() with {
        address < (local::FlashSize - size);
      };
      trans_prog.display();

      spiflash_program(
        sif.tb,
        trans_prog.cmd,
        trans_prog.address,
        trans_prog.addr_mode,
        trans_prog.program_data
      );

      wait_trans();

      // while Read Status BUSY cleared
      do begin
        #100ns
        read_status();
        busy = status[0][0];
      end while (busy == 1'b 1);

      // Update mirrored_storage
      if (wel) update_storage_with_trans(trans_prog);

      // Read from Mailbox space only when WEL
      trans_size = $min(trans_prog.size, 256);
      trans_read = new();
      trans_read.randomize() with {
        address == local::MailboxAddr;
        addr_mode == 1'b 0; // 3B
        size == local::trans_size;
      };

      spiflash_read(
        sif.tb,
        trans_read.cmd,
        trans_read.address,
        trans_read.addr_mode,
        trans_read.dummy,
        trans_read.size,
        trans_read.io_mode,
        rdata_mbx
      );

      wait_trans();

      // Read from SPIFlash (to the original address)
      // Read even if wel = 0. Check if value is written?

      trans_read = new();
      trans_read.randomize() with {
        address == local::trans_prog.address;
        addr_mode == 1'b 0; // 3B
        size == local::trans_size;
      };

      spiflash_read(
        sif.tb,
        trans_read.cmd,
        trans_read.address,
        trans_read.addr_mode,
        trans_read.dummy,
        trans_read.size,
        trans_read.io_mode,
        rdata_spiflash
      );

      wait_trans();

      // Compare all three buffers!

      rdata_mbx.delete();
      rdata_spiflash.delete();

    end

  endtask : test_program

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

  function automatic void update_storage_with_trans(
    SpiTransProgram trans
  );
    automatic int unsigned start_idx;
    automatic int unsigned trans_size = $min(256, trans.size);
    automatic logic [31:0] trans_addr = {trans.address[31:8], 8'h0};
    automatic logic [7:0] trans_offset = trans.address[7:0];

    start_idx = (trans.size > 256) ? (trans.size % 256) : 0;
    for (int unsigned i = 0 ; i < trans_size ; i++) begin
      write_byte(
        trans_addr + ((trans_offset + i)%256),
        trans.program_data[start_idx+i]
      );
    end
  endfunction : update_storage_with_trans

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
        $display("Data mismatch: Addr{%8Xh} EXP(%2Xh) / RCV(%2Xh)",
          addr+i, read_byte(addr+i), data[i]);
      end
    end
    return pass;
  endfunction : compare_storage

endprogram : prog_passthrough_host
