// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Behavioral model of SPI Flash

program spiflash #(
  parameter int unsigned FlashSize = 1024*1024, // 1MB

  // Num of Repeating Continuous Code ('h7F)
  parameter int unsigned CcNum    = 7,
  parameter logic [7:0]  JedecId  = 8'h 1F,
  parameter logic [15:0] DeviceId = 16'h 1234,

  // Command Support
  parameter bit EnFastReadDual = 1'b 1,
  parameter bit EnFastReadQuad = 1'b 1,

  // Dummy Cycle
  parameter int unsigned DummySizeNormal = 8,
  parameter int unsigned DummySizeDual   = 4,
  parameter int unsigned DummySizeQuad   = 2
) (
  input logic sck,
  input logic csb,
  inout [3:0] sd
  // TODO: Add WP
);

  typedef enum bit {
    Addr3B,
    Addr4B
  } addr_mode_e;

  // Return Output mode
  typedef enum int unsigned {
    IoSingle,
    IoDual,
    IoQuad
  } io_mode_e;

  typedef logic [7:0] spiflash_byte_t;

  localparam spiflash_byte_t Cc = 8'h 7F;

  localparam int unsigned StorageAw = $clog2(FlashSize);

  // spiflash_addr_t is the smallest address width to represent FlashSize bytes
  typedef logic [StorageAw-1:0] spiflash_addr_t;

  logic [3:0] sd_out, sd_en;

  assign sd[0] = sd_en[0] ? sd_out[0] : 1'b z;
  assign sd[1] = sd_en[1] ? sd_out[1] : 1'b z;
  assign sd[2] = sd_en[2] ? sd_out[2] : 1'b z;
  assign sd[3] = sd_en[3] ? sd_out[3] : 1'b z;

  // SPI Flash internal state variables
  addr_mode_e     addr_mode;
  spiflash_byte_t [2:0] status; // 24 bit
  spiflash_byte_t storage[spiflash_addr_t]; // Associative Array to store data

  initial begin
    print_banner();

    // Init values
    status = '0;
    // Should wait ??
    main();
  end

  function automatic void print_banner();
    $display("/////////////////////");
    $display("// SPI Flash Model //");
    $display("/////////////////////");

    // Print current config
    $display("");
    $display("Configurations:");
    $display("  JEDEC ID:  ID(0x%2X) CC_NUM (%2d)", JedecId, CcNum);
    $display("  Capacity:  %s", print_capacity(FlashSize));
    $display("  Fast Read: %s/ Dummy Cycle (%1d)",
      "Enabled", DummySizeNormal);
    $display("  Dual Mode:%s/ Dummy Cycle (%1d)",
      (EnFastReadDual) ? "Enabled" : "Disabled", DummySizeDual);
    $display("  Quad Mode:%s/ Dummy Cycle (%1d)",
      (EnFastReadQuad) ? "Enabled" : "Disabled", DummySizeQuad);
  endfunction : print_banner

  function automatic string print_capacity(int unsigned size);
    string str;
    // Get the highest unit (GB, MB, kB)
    automatic int unsigned quotient;
    automatic int unsigned order; // 0: B, 1: kB, 2: MB, 3: GB
    automatic string unit;
    quotient = size;
    forever begin
      if (quotient < 1024) break;
      quotient = quotient / 1024;
      order = order + 1;
    end

    case (order)
      0: unit = "B";
      1: unit = "kB";
      2: unit = "MB";
      3: unit = "GB";
      4: unit = "TB";
      default: unit = "Unsupported";
    endcase

    str = $sformatf("%0d%s", quotient, unit);
    return str;
  endfunction : print_capacity

  static task main();
    // Main function
    forever begin
      automatic spiflash_byte_t opcode;
      automatic bit             early_termination;
      automatic int unsigned    excessive_sck = 0;
      // Big loop. Wait transaction
      sd_en = 4'h 0; // Off the output by default
      wait(csb == 1'b 0);
      early_termination = 1'b 0;
      fork
        begin
          // If cmd process comes first, this forked process won't set
          // early_termination bit
          @(posedge csb);
          early_termination = 1'b 1;
        end
        begin
          // Main
          cmdparse(opcode); // Store incoming into opcod
          process_cmd(opcode);

          // Count remaining edges of SCK. opcode completed command should
          // have no additional data, or should be discarded
          sd_en = 4'h 0;
          forever begin
            @(posedge sck);
            excessive_sck++;
          end
        end
      join_any
      // Float the line
      sd_en = 4'h 0;

      // Determine early termination, if not early terminated, the main block
      // waits CSb de-assertion too
      // For many Output commands, the logic sends data until host releases
      // CSb. In this case, early_termination is set too. If the command is
      // output command, do not process early_termination.

      // Process program, etc
      // If excessive sck, then discard.

      // Kill the forked process
      disable fork;
    end
  endtask : main

  task automatic cmdparse(
    output spiflash_byte_t opcode
  );
    automatic spiflash_byte_t spi_byte = 0;
    // Receive first 8 beats and decoding the byte, call subsequence tasks.
    repeat(8) begin
      @(posedge sck);
      spi_byte = {spi_byte[6:0], sd[0]};
    end
    @(negedge sck); // Wait the data line fully completed
    $display("SPIFlash: Command(%2Xh) received", spi_byte);
    opcode = spi_byte;
  endtask : cmdparse

  task automatic process_cmd(
    input spiflash_byte_t opcode
  );
    // Main case block to call subtasks depending on the opcode
    case (opcode)
      spi_device_pkg::CmdReadStatus1: begin
        // Return status data
        return_status(0); // 0-2
      end

      spi_device_pkg::CmdJedecId: begin
        return_jedec();
      end
    endcase

  endtask : process_cmd

  task automatic return_byte(spiflash_byte_t data, io_mode_e io_mode);
    // Assume the task is called at @(negedge sck);
    automatic int unsigned rails;
    automatic logic [7:0]  lines;
    case (io_mode)
      IoSingle: begin
        rails = 1;
        sd_en = 4'b 0010;
      end
      IoDual: begin
        rails = 2;
        sd_en = 4'b 0011;
      end
      IoQuad: begin
        rails = 4;
        sd_en = 4'b 1111;
      end
      default: begin
        rails = 1;
        sd_en = 4'b 0010;
      end
    endcase

    lines = data;
    repeat(8/rails) begin
      case (io_mode)
        IoSingle: begin
          sd_out[1] = lines[7];
          lines = {lines[6:0], 1'b 0};
        end
        IoDual: begin
          sd_out[1:0] = lines[7:6];
          lines = {lines[5:0], 2'b 00};
        end
        IoQuad: begin
          sd_out[3:0] = lines[7:4];
          lines = {lines[3:0], 4'b 0000};
        end
        default: begin
          sd_out[1] = lines[7];
          lines = {lines[6:0], 1'b 0};
        end
      endcase
      @(negedge sck);
    end
  endtask : return_byte

  task automatic return_status(int unsigned idx);
    // Starting from the index and wraps %3 until host releases CSb
    automatic int unsigned s_idx = idx;
    forever begin
      return_byte(status[s_idx], IoSingle);
      s_idx = (s_idx + 1)%3;
    end
  endtask : return_status

  task automatic return_jedec();
    // Repeat CcNum then JedecId and DeviceId(MSB to LSB)
    repeat (CcNum) begin
      return_byte(Cc, IoSingle);
    end
    return_byte(JedecId, IoSingle);
    return_byte(DeviceId[ 7:0], IoSingle);
    return_byte(DeviceId[15:8], IoSingle);
    // Float
  endtask : return_jedec

endprogram : spiflash
