// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

`define DPSRAM_DATA(x) tb.dut.u_memory_2p.u_mem.gen_generic.u_impl_generic.mem[(x)]

program prog_passthrough_sw
  import spid_common::*;
(
  input logic clk,
  input logic rst_n,

  output tlul_pkg::tl_h2d_t h2d,
  input  tlul_pkg::tl_d2h_t d2h
);

  initial begin
    automatic string testname;

    h2d = tlul_pkg::TL_H2D_DEFAULT;

    // Wait reset relase
    @(posedge rst_n);
    #10ns
    @(posedge clk);
    $display("Intializing SPI_DEVICE: PassThrough mode");
    init_spidevice_passthrough();

    $value$plusargs("TESTNAME=%s", testname);

    case (testname)
      "readbasic": begin
      end

      "addr_4b": begin
      end

      "wel": begin
      end

      "program": begin
        // Need to disable Status return from SPI_DEVICE and issue directly to
        // SPIFlash
        test_program();
      end
    endcase

    forever begin
      @(posedge clk);
    end
  end

  task automatic init_spidevice_passthrough(
  );
    automatic logic [31:0] csr_wdata;
    automatic logic [31:0] csr_rdata;
    // Initialize SPI_DEVICE as in Passthrough mode
    // - Switch SRAM clock
    // - Program SpiMode
    // - Configure CMD_INFO entries
    // - Configure intercept (can be changed later)
    // - address swap, payload swap for a specific CMD_INFO entry
    // - Initialize DPSRAM

    tlul_write(
      clk,
      h2d,
      d2h,
      32'(spi_device_reg_pkg::SPI_DEVICE_CFG_OFFSET),
      32'h 0100_0000, // mailbox_en := 1
      4'b 1111
    );

    tlul_write(
      clk,
      h2d,
      d2h,
      32'(spi_device_reg_pkg::SPI_DEVICE_MAILBOX_ADDR_OFFSET),
      32'h 00CD_E000,
      4'b 1111
    );

    csr_wdata = '0;
    csr_wdata[5:4] = spi_device_pkg::PassThrough;
    tlul_write(
      clk,
      h2d,
      d2h,
      32'(spi_device_reg_pkg::SPI_DEVICE_CONTROL_OFFSET),
      csr_wdata,
      4'b 1111
    );
    csr_wdata[31] = 1'b 1;
    tlul_write(
      clk,
      h2d,
      d2h,
      32'(spi_device_reg_pkg::SPI_DEVICE_CONTROL_OFFSET),
      csr_wdata,
      4'b 1111
    );

    // JEDEC ID: Slightly differ from spiflash behavioral model
    tlul_write(
      clk, h2d, d2h,
      32'(spi_device_reg_pkg::SPI_DEVICE_JEDEC_CC_OFFSET),
      '0, // FIXME: Correct CC num and CC
      4'b 1111
    );
    tlul_write(
      clk, h2d, d2h,
      32'(spi_device_reg_pkg::SPI_DEVICE_JEDEC_ID_OFFSET),
      '0, // FIXME: Google JEDEC ID here
      4'b 1111
    );

    // INTERCEPT for Read Status
    // WREN/ WRDI are processed inside SPI_DEVICE IP, by turning the intercept
    // on, host system can check if WEL set/clear correctly.
    tlul_write(
      clk, h2d, d2h,
      32'(spi_device_reg_pkg::SPI_DEVICE_INTERCEPT_EN_OFFSET),
      32'h 0000_0009, // MBX, STATUS
      4'b 0001
    );

    // FILTER
    // Read STATUS filtered.
    // WREN/ WRDI go through as no SPI_HOST IP in TB yet.
    // PROGRAM/ BLOCK ERASE go through as same reason as WREN/ WRDI
    tlul_write(
      clk, h2d, d2h,
      32'(spi_device_reg_pkg::SPI_DEVICE_CMD_FILTER_0_OFFSET),
      32'h 0000_0020, // [5] := 1
      4'b 1111
    );

    // CMD_INFO
    init_cmdinfo_list();

    init_dpsram();

  endtask : init_spidevice_passthrough

  task automatic init_cmdinfo_list();
    automatic logic [31:0] cmdinfo_wdata;
    // Init CMD_INFO entries
    // 0:23 normal CMD_INFO
    // 24:27 valid, opcode only (EN4B/ EX4B/ WREN/ WRDI)
    cmdinfo_wdata  = '0; // default

    for (int unsigned i = 0 ; i < spi_device_reg_pkg::NumCmdInfo; i++) begin
      cmdinfo_wdata[7:0]   = CmdInfo[i].opcode         ;
      cmdinfo_wdata[9:8]   = CmdInfo[i].addr_mode      ;
      cmdinfo_wdata[10]    = CmdInfo[i].addr_swap_en   ;
      cmdinfo_wdata[11]    = CmdInfo[i].mbyte_en       ;
      cmdinfo_wdata[14:12] = CmdInfo[i].dummy_size     ;
      cmdinfo_wdata[15]    = CmdInfo[i].dummy_en       ;
      cmdinfo_wdata[19:16] = CmdInfo[i].payload_en     ;
      cmdinfo_wdata[20]    = CmdInfo[i].payload_dir    ;
      cmdinfo_wdata[21]    = CmdInfo[i].payload_swap_en;
      cmdinfo_wdata[24]    = CmdInfo[i].upload         ;
      cmdinfo_wdata[25]    = CmdInfo[i].busy           ;
      cmdinfo_wdata[31]    = CmdInfo[i].valid          ;
      tlul_write(
        clk,
        h2d,
        d2h,
        32'(spi_device_reg_pkg::SPI_DEVICE_CMD_INFO_0_OFFSET + (i<<2)),
        cmdinfo_wdata,
        4'b 1111
      );
    end

    for (int unsigned i = 0 ;
      i < (spi_device_pkg::NumTotalCmdInfo-spi_device_reg_pkg::NumCmdInfo);
      i++) begin
      tlul_write(
        clk,
        h2d,
        d2h,
        32'(spi_device_reg_pkg::SPI_DEVICE_CMD_INFO_EN4B_OFFSET+(i<<2)),
        32'h 8000_0000 | CmdInfo[24+i].opcode,
        4'b 1111
      );
    end

  endtask : init_cmdinfo_list

  function automatic void init_dpsram(bit randomness = 1'b 1);
    // Fill the DPSRAM with random or predefined data
    // To reduce the sim time, used force value
    automatic logic [35:0] sram_data;
    automatic logic [31:0] strip_data;
    for (int unsigned i = 0; i < spi_device_pkg::SramDepth; i++) begin
      if (randomness) begin
        strip_data = $urandom();
      end else begin
        strip_data = {8'(i*4+3), 8'(i*4+2), 8'(i*4+1), 8'(i*4)};
      end
      // Add Odd Parity
      for (int unsigned j = 0 ; j < 4 ; j++) begin
        strip_data[j*9+8] = ~(^strip_data[j*9+:8]);
      end
      `DPSRAM_DATA(i) = strip_data;
    end
  endfunction : init_dpsram

  static task test_program();
    // Turning off INTERCEPT
    tlul_write(
      clk, h2d, d2h,
      32'(spi_device_reg_pkg::SPI_DEVICE_INTERCEPT_EN_OFFSET),
      32'h 0000_0008, // [3] := MBX
      4'b 0001
    );

    // FILTER
    // Turn off Read Status / Page Program commands filter
    tlul_write(
      clk, h2d, d2h,
      32'(spi_device_reg_pkg::SPI_DEVICE_CMD_FILTER_0_OFFSET),
      32'h 0000_0000, // [5] := 0 / [2] := 0
      4'b 1111
    );

  endtask : test_program

endprogram : prog_passthrough_sw
