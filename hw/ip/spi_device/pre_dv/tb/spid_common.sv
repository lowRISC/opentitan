// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI Device common tasks, functions
interface spi_if (input clk);
  logic csb;
  logic [3:0] sd_in;
  logic [3:0] sd_out;

  modport tb  (input clk, output csb, output sd_in, input sd_out);
  modport dut (input clk, input  csb, input  sd_in, output sd_out);
endinterface : spi_if

interface spiflash_if;
  wire       sck;
  wire       csb;
  wire [3:0] sd;

  modport host   (output sck, output csb, inout sd);
  modport device (input  sck, input  csb, inout sd);
endinterface : spiflash_if

// spid_common package contains common tasks, functions
package spid_common;
  import spi_device_pkg::*;

  typedef enum int unsigned {
    IoNone   = 0,
    IoSingle = 1,
    IoDual   = 2,
    IoQuad   = 3
  } mode_e;

  typedef enum int unsigned {
    DirNone  = 0,
    DirIn    = 1,
    DirOut   = 2,
    DirInout = 3, // Only with IoSingle
    DirZ     = 4
  } dir_e;

  typedef logic [7:0] spi_data_t;

  typedef spi_data_t spi_queue_t [$];

  typedef struct packed {
    spi_data_t data;
    mode_e     mode;

    // DIR can change from:
    //     SPI Flash:   DirIn
    //     SPI Flash:   DirIn -> {DirZ} -> DirOut
    //     SPI Generic: DirInout
    //     TPM:         DirIn -> DirInout -> DirIn
    //     TPM:         DirIn -> DirInout -> DirOut -> DirIn
    //     TPM:         DirIn -> DirInout -> DirOut
    //
    // When DirOut, the TB stacks the spi_if into fifo data
    dir_e       dir;
  } spi_fifo_t;

  typedef struct packed {
    logic generic_rx_full;
    logic generic_rx_watermark;
    logic generic_tx_watermark;
    logic generic_rx_error;
    logic generic_rx_overflow;
    logic generic_tx_underflow;
    logic upload_cmdfifo_not_empty;
    logic upload_payload_not_empty;
    logic upload_payload_overflow;
    logic readbuf_watermark;
    logic readbuf_flip;
    logic tpm_header_not_empty;
  } interrupt_t;

  // Register parameters
  parameter int unsigned BitCmdfifoNotEmpty  = 6;
  parameter int unsigned BitReadbufWatermark = 9;
  parameter int unsigned BitReadbufFlip      = 10;

  // Command list parameters
  import spi_device_pkg::cmd_info_t;
  import spi_device_pkg::NumTotalCmdInfo;

  parameter cmd_info_t [NumTotalCmdInfo-1:0] CmdInfo = {
    // 27: WRDI
    '{
      valid:            1'b 1,
      opcode:           8'h 04,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0001, // MISO
      payload_dir:      PayloadIn,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0

    },
    // 26: WREN
    '{
      valid:            1'b 1,
      opcode:           8'h 06,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0001, // MISO
      payload_dir:      PayloadIn,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0

    },
    // 25: EX4B
    '{
      valid:            1'b 1,
      opcode:           8'h E9,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 24: EN4B
    '{
      valid:            1'b 1,
      opcode:           8'h B7,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 23: Read JEDEC ID
    '{
      valid:            1'b 1,
      opcode:           8'h 9F,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 22:
    '{
      valid:            1'b 0,
      opcode:           8'h E7,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 21:
    '{
      valid:            1'b 0,
      opcode:           8'h E8,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 20:
    '{
      valid:            1'b 0,
      opcode:           8'h E9,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 19:
    '{
      valid:            1'b 0,
      opcode:           8'h EA,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 18:
    '{
      valid:            1'b 0,
      opcode:           8'h EB,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 17:
    '{
      valid:            1'b 0,
      opcode:           8'h EC,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 16:
    '{
      valid:            1'b 0,
      opcode:           8'h EF,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 15:
    '{
      valid:            1'b 0,
      opcode:           8'h F0,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 14:
    '{
      valid:            1'b 0,
      opcode:           8'h F1,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 13: Upload Cmd & Addr & Payload
    '{
      valid:            1'b 1,
      opcode:           8'h 02,
      addr_mode:        AddrCfg,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0001, // MISO
      payload_dir:      PayloadIn,
      payload_swap_en:  1'b 0,
      upload:           1'b 1,
      busy:             1'b 1
    },

    // 12: Upload Cmd & Addr
    '{
      valid:            1'b 1,
      opcode:           8'h 52, // block erase (32kB)
      addr_mode:        AddrCfg,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0000, // MISO
      payload_dir:      PayloadIn,
      payload_swap_en:  1'b 0,
      upload:           1'b 1,
      busy:             1'b 1
    },

    // 11: Upload Cmd Only
    '{
      valid:            1'b 1,
      opcode:           8'h C7, // chip erase
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0000, // MISO
      payload_dir:      PayloadIn,
      payload_swap_en:  1'b 0,
      upload:           1'b 1,
      busy:             1'b 1
    },

    // 10: ReadCmd 6 TODO
    '{
      valid:            1'b 0,
      opcode:           8'h F5,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 9: ReadCmd 5 TODO
    '{
      valid:            1'b 0,
      opcode:           8'h F6,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 8: ReadCmd 4 Fast Read Quad
    '{
      valid:            1'b 1,
      opcode:           8'h 6B,
      addr_mode:        AddrCfg,
      addr_swap_en:     1'b 1,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 1,
      dummy_size:        'h 2,
      payload_en:       4'b 1111, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 7: ReadCmd 3 Fast Read Dual
    '{
      valid:            1'b 1,
      opcode:           8'h 3B,
      addr_mode:        AddrCfg,
      addr_swap_en:     1'b 1,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 1,
      dummy_size:        'h 3,
      payload_en:       4'b 0011, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 6: ReadCmd 2 Fast Read
    '{
      valid:            1'b 1,
      opcode:           8'h 0B,
      addr_mode:        AddrCfg,
      addr_swap_en:     1'b 1,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 1,
      dummy_size:        'h 7,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 5: ReadCmd 1 Normal Read
    '{
      valid:            1'b 1,
      opcode:           8'h 03,
      addr_mode:        AddrCfg,
      addr_swap_en:     1'b 1,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 4: ReadSfdp
    '{
      valid:            1'b 1,
      opcode:           8'h 5A,
      addr_mode:        Addr3B,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 1,
      dummy_size:       3'h 7,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 3: CmdInfoReadJedecId
    '{
      valid:            1'b 1,
      opcode:           8'h 9F,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 2: CmdInfoReadStatus3
    '{
      valid:            1'b 1,
      opcode:           8'h 15,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 1: CmdInfoReadStatus2
    '{
      valid:            1'b 1,
      opcode:           8'h 35,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    },

    // 0: CmdInfoReadStatus1
    '{
      valid:            1'b 1,
      opcode:           8'h 05,
      addr_mode:        AddrDisabled,
      addr_swap_en:     1'b 0,
      mbyte_en:         1'b 0,
      dummy_en:         1'b 0,
      dummy_size:          '0,
      payload_en:       4'b 0010, // MISO
      payload_dir:      PayloadOut,
      payload_swap_en:  1'b 0,
      upload:           1'b 0,
      busy:             1'b 0
    }
  };

  // Temporarily only two cmds specified here
  parameter logic [7:0] OpcodeCmdOnly [2] = '{
    8'h C7, // Chip Erase
    8'h 06  // Write Enable
  };

  parameter logic [7:0] OpcodeCmdAddr [2] = '{
    8'h 52, // Block Erase (32kB)
    8'h D8  // Block Erase (64kB)
  };

  parameter logic [7:0] OpcodeCmdAddrPayload [2] = '{
    8'h 02, // Page Program
    8'h 42  // Program Security Register
  };

  parameter logic [7:0] OpcodeCmdPayload [2] = '{
    8'h 01, // Write Status 1
    8'h 11  // Write Status 3
  };

  parameter int unsigned OffsetW = $clog2(SramStrbW);
  parameter int unsigned PayloadByte = SramPayloadDepth * (SramDw/8);

  // spi_transaction: Send/ Receive data using data fifo.
  task automatic spi_transaction(
    virtual spi_if.tb sif,
    ref spi_fifo_t  d_in [$],
    ref spi_queue_t d_out
  );
    automatic spi_data_t char;
    automatic mode_e     mode;
    automatic dir_e      dir;
    automatic spi_data_t rcv_byte;

    // Assert CSb
    spi_start(sif);

    // pop data from `d_in[$]`
    foreach (d_in[i]) begin
      //$display("Popped from d_in[%d]: %x", i, d_in[i].data);

      if (d_in[i].dir != DirNone) begin
        // TODO: check the dir sequence.
        dir = d_in[i].dir;
      end

      if (d_in[i].mode != IoNone) begin
        mode = d_in[i].mode;
      end

      case (dir)
        DirNone: begin
          // Should error
          $error("DirNone sequence is not allowed");
        end

        DirIn: begin
          // Host -> DUT
          spi_sendbyte(sif, d_in[i].data, mode);
        end

        DirZ: begin
          // High-Z Explicit float and wait a cycle
          // It has no byte concept here.
          spi_highz(sif);
        end

        DirInout: begin
          // Assume the mode is Single mode
          assert(mode == IoSingle);
          spi_sendandreceive(sif, d_in[i].data, rcv_byte);

          d_out.push_back(rcv_byte);
        end

        DirOut: begin
          // Device -> Host
          spi_receivebyte(sif, rcv_byte, mode);

          d_out.push_back(rcv_byte);
        end
      endcase
    end

    // De-assert CSb
    spi_end(sif);
    sif.sd_in[3:0] = 'Z; // make float
  endtask : spi_transaction

  // spi_start: assert CSb to start transaction
  task automatic spi_start(virtual spi_if.tb sif);
    // wait until negedge of SCK
    @(negedge sif.clk);
    sif.csb = 1'b 0;
  endtask : spi_start

  // spi_end: de-assert CSb to end SPI transaction
  task automatic spi_end(virtual spi_if.tb sif);
    // It is always assumed to call `spi_end()` at the negedge of SCK
    // Wait then deassert
    @(posedge sif.clk);
    sif.csb <= 1'b 1;
  endtask : spi_end

  // spi_sendbyte: Send 8bit byte to DUT
  task automatic spi_sendbyte(
    virtual spi_if.tb sif,
    input spi_data_t  data,
    input mode_e      mode
  );
    // Assume the function called at negedge of CSb.
    // Drive the data right away
    sif.sd_in[3:0] = 'Z;
    case (mode)
      IoSingle: begin
        // from 7 -> 0
        for (int i = 7 ; i >= 0 ; i--) begin
          sif.sd_in[0] = data[i];
          @(negedge sif.clk);
        end
      end

      IoDual: begin
        for (int i = 6 ; i >= 0 ; i=i-2) begin
          sif.sd_in[1:0] = data[i+:2];
          @(negedge sif.clk);
          if (i == 0 ) break;
        end
      end

      IoQuad: begin
        for (int i = 4 ; i >= 0 ; i=i-4) begin
          sif.sd_in[3:0] = data[i+:4];
          @(negedge sif.clk);
        end
      end
    endcase

    //$display("SPI Byte sent!: %x", data);
  endtask: spi_sendbyte

  // spi_highz floats the lines for one cycle.
  task automatic spi_highz(virtual spi_if.tb sif);
    sif.sd_in[3:0] = 4'h z;

    @(negedge sif.clk);
  endtask : spi_highz

  task automatic spi_sendandreceive(
    virtual spi_if.tb sif,
    input  spi_data_t send_byte,
    output spi_data_t rcv_byte
  );
    for (int i = 7 ; i >= 0 ; i--) begin
      sif.sd_in[0] = send_byte[i];
      @(posedge sif.clk);
      rcv_byte[i] = sif.sd_out[1];
      @(negedge sif.clk);
    end

    //$display("SPI Byte Sent/Received!: %x / %x", send_byte, rcv_byte);

  endtask : spi_sendandreceive

  task automatic spi_receivebyte(
    virtual spi_if.tb sif,
    output spi_data_t rcv_byte,
    input mode_e      mode
  );
    // Assume it is changed to receive mode
    sif.sd_in[3:0] = 4'h z;

    case (mode)
      IoSingle: begin
        for (int i = 7 ; i >= 0 ; i--) begin
          @(posedge sif.clk);
          rcv_byte[i] = sif.sd_out[1]; //MISO
        end
      end

      IoDual: begin
        for (int i = 6 ; i >= 0 ; i=i-2) begin
          @(posedge sif.clk);
          rcv_byte[i+:2] = sif.sd_out[0+:2];
        end
      end

      IoQuad: begin
        for (int i = 4 ; i >= 0 ; i=i-4) begin
          @(posedge sif.clk);
          rcv_byte[i+:4] = sif.sd_out[0+:4];
        end
      end
    endcase

    //$display("SPI Byte Received: %x", rcv_byte);

    // Always end with negative edge to complete the byte
    @(negedge sif.clk);

  endtask : spi_receivebyte

  ////////////////////////
  // SPI Flash Commands //
  ////////////////////////
  task automatic spiflash_readstatus(
    virtual spi_if.tb sif,
    input  spi_data_t opcode,
    output spi_data_t status
  );
    automatic spi_fifo_t send_data [$];
    automatic spi_data_t rcv_data [$];

    assert(opcode inside {8'h 05, 8'h 35, 8'h 15});

    send_data.push_back('{data: opcode, dir: DirIn,  mode: IoSingle});
    send_data.push_back('{data: '0,     dir: DirOut, mode: IoNone  });

    spi_transaction(sif, send_data, rcv_data);

    status = rcv_data.pop_front();

    $display("Status Received: %x", status);

  endtask : spiflash_readstatus

  task automatic spiflash_oponly(
    virtual spi_if.tb sif,
    input spi_byte_t opcode
  );
    // OPCODE only commands
    automatic spi_fifo_t send_data [$];
    automatic spi_data_t rcv_data [$];

    send_data.push_back('{data: opcode, dir: DirIn,  mode: IoSingle});
    spi_transaction(sif, send_data, rcv_data);

  endtask : spiflash_oponly

  task automatic spiflash_wren(
    virtual spi_if.tb sif,
    input spi_byte_t opcode
  );
    spiflash_oponly(sif, opcode);
    $display("WREN sent!");

  endtask : spiflash_wren

  task automatic spiflash_wrdi(
    virtual spi_if.tb sif,
    input spi_byte_t opcode
  );
    spiflash_oponly(sif, opcode);
    $display("WRDI sent!");

  endtask : spiflash_wrdi

  task automatic spiflash_readjedec(
    virtual spi_if.tb   sif,
    input  spi_data_t   opcode,
    input  logic [7:0]  cc,      // Continuous Code
    output int unsigned num_cc,
    ref    logic [23:0] jedec_id // [23:16] Manufacurer ID, [15:0] ID
  );
    // as the transaction size of Read JEDEC ID depends on the Continuous Code,
    // This task does not follow the conventional SPI transaction commands.
    // They use `spi_transaction()` task to send/ receive command and payload.
    //
    // This task directly calls `spi_start()`, `spi_sendbyte()`,
    // `spi_receivebyte()`.
    automatic spi_fifo_t send_data [$];
    automatic spi_data_t rcv_data  [$];
    automatic spi_data_t rcv_byte;
    automatic int unsigned cc_cnt = 0;

    assert(opcode == 8'h 9F);

    // Assert CSb
    spi_start(sif);

    // Send opcode
    spi_sendbyte(sif, opcode, IoSingle);

    // Receive a Byte then check if Cc, then repeat
    do begin
      spi_receivebyte(sif, rcv_byte, IoSingle);
      cc_cnt++;
    end while (rcv_byte == cc);

    num_cc = cc_cnt - 1;

    // If not matched with CC, then that is the Manufacture ID
    jedec_id[23:16] = rcv_byte;

    spi_receivebyte(sif, rcv_byte, IoSingle);
    jedec_id[7:0] = rcv_byte;
    spi_receivebyte(sif, rcv_byte, IoSingle);
    jedec_id[15:8] = rcv_byte;

    // De-assert CSb
    spi_end(sif);

    $display("Jedec ID Received: Manufacturer ID [%x], JEDEC_ID [%x]",
      jedec_id[23:16], jedec_id[15:0]);

  endtask : spiflash_readjedec

  task automatic spiflash_chiperase(
    virtual spi_if.tb  sif,
    input spi_data_t   opcode
  );
    automatic spi_fifo_t send_data [$];
    automatic spi_data_t rcv_data  [$];

    send_data.push_back('{data: opcode, dir: DirIn,  mode: IoSingle});

    spi_transaction(sif, send_data, rcv_data);

    $display("Chip Erase (%x) is sent", opcode);

  endtask : spiflash_chiperase

  task automatic spiflash_blockerase(
    virtual spi_if.tb  sif,
    input spi_data_t   opcode,
    input logic [31:0] addr,
    input bit          addr_4b_en
  );
    automatic spi_fifo_t send_data [$];
    automatic spi_data_t rcv_data  [$];

    send_data.push_back('{data: opcode, dir: DirIn, mode: IoSingle});
    if (addr_4b_en) begin
      send_data.push_back('{data: addr[31:24], dir: DirNone, mode: IoNone});
    end
    for (int i = 2 ; i >= 0; i--) begin
      send_data.push_back('{data: addr[8*i+:8], dir: DirNone, mode: IoNone});
    end

    spi_transaction(sif, send_data, rcv_data);

    if (addr_4b_en) begin
      $display("Block Erase (%Xh) command is sent. 32bit addr (%Xh)",
        opcode, addr);
    end else begin
      $display("Block Erase (%Xh) command is sent. 24bit addr (%Xh)",
        opcode, addr[23:0]);
    end

  endtask : spiflash_blockerase

  task automatic spiflash_program(
    virtual spi_if.tb sif,
    input spi_data_t  opcode,
    input logic [31:0] addr,
    input bit          addr_4b_en,
    input spi_queue_t  payload
  );
    automatic spi_fifo_t send_data [$];
    automatic spi_data_t rcv_data  [$];

    send_data.push_back('{data: opcode, dir: DirIn, mode: IoSingle});
    if (addr_4b_en) begin
      send_data.push_back('{data: addr[31:24], dir: DirNone, mode: IoNone});
    end
    for (int i = 2 ; i >= 0; i--) begin
      send_data.push_back('{data: addr[8*i+:8], dir: DirNone, mode: IoNone});
    end

    // Payload
    foreach (payload[i]) begin
      send_data.push_back('{
        data: payload[i],
        dir:  DirNone,
        mode: IoNone
      });
    end

    spi_transaction(sif, send_data, rcv_data);

    $display("Program cmd (%Xh) to Addr (%Xh) is sent.",
      opcode, (addr_4b_en) ? addr : addr[23:0]);

    foreach (payload[i]) begin
      $display("Payload %d : %Xh", i, payload[i]);
    end

  endtask : spiflash_program

  task automatic spiflash_readsfdp(
    virtual spi_if.tb  sif,
    input spi_data_t   opcode,
    input logic [23:0] addr,
    input int          size, // #bytes
    ref   spi_queue_t  payload
  );
    automatic spi_fifo_t  send_data [$];
    automatic spi_queue_t rcv_data;
    automatic spi_data_t  rcv_byte;

    // opcode
    send_data.push_back('{data: opcode, dir: DirIn, mode: IoSingle});
    // address
    for (int i = 2 ; i >= 0 ; i--) begin
      send_data.push_back('{data: addr[8*i+:8], dir: DirNone, mode: IoNone});
    end

    // dummy (8 cycles)
    repeat(8) begin
      send_data.push_back('{data: 'z, dir: DirZ, mode: IoNone});
    end

    // Receive data
    repeat(size) begin
      send_data.push_back('{data: '0, dir: DirOut, mode: IoSingle});
    end

    spi_transaction(sif, send_data, rcv_data);

    assert(rcv_data.size() == size);

    $display("Read SFDP [0x%8x + 0x%4x]", addr, size);

    repeat (size) begin
      rcv_byte = rcv_data.pop_front();
      payload.push_back(rcv_byte);
    end

  endtask : spiflash_readsfdp

  task automatic spiflash_read(
    virtual spi_if.tb  sif,
    input spi_data_t   opcode,
    input logic [31:0] addr,
    input bit          addr_mode,
    input int unsigned dummy,
    input int unsigned size,
    input mode_e       io_mode,
    ref spi_queue_t    payload
  );
    automatic spi_fifo_t  send_data [$];
    automatic spi_queue_t rcv_data;

    // opcode
    send_data.push_back('{data: opcode, dir: DirIn, mode: IoSingle});

    // address
    for (int i = 2 + addr_mode ; i >= 0 ; i--) begin : address
      send_data.push_back('{data: addr[8*i+:8], dir: DirNone, mode: IoNone});
    end

    // dummy
    for (int i = dummy ; i > 0 ; i--) begin : dummy_logic
      send_data.push_back('{data: 'z, dir: DirZ, mode: IoNone});
    end

    // receive data
    repeat(size) begin
      send_data.push_back('{data: '0, dir: DirOut, mode: io_mode});
    end

    spi_transaction(sif, send_data, rcv_data);

    assert(rcv_data.size() == size);

    $display("Read Cmd [0x%8x + 0x%4x]", addr, size);

    assert(payload.size() == 0);

    // OR, push_back foreach?
    foreach (rcv_data[i]) begin
      payload.push_back(rcv_data[i]);
    end

  endtask : spiflash_read

  task automatic spiflash_addr_4b(
    virtual spi_if.tb  sif,
    input spi_data_t   opcode
  );
    spiflash_oponly(sif, opcode);

  endtask : spiflash_addr_4b


  //===========================================================================
  // SW-side functions/ tasks
  // SRAM interface
  task automatic sram_readword(
    const ref logic clk,

    ref sram_l2m_t       l2m,
    const ref logic      gnt,
    const ref sram_m2l_t m2l,

    input  logic [SramAw-1:0] addr,
    output logic [SramDw-1:0] rdata
  );
    l2m.req   = 1'b 1;
    l2m.addr  = addr;
    l2m.we    = 1'b 0;
    l2m.wdata = '0;
    l2m.wstrb = '0;

    @(posedge clk iff gnt == 1'b 1);
    l2m.req   = 1'b 0;
    // Check if rvalid?
    while (m2l.rvalid == 1'b 0) begin
      @(posedge clk);
    end
    rdata = m2l.rdata;
    assert(m2l.rerror == '0);

  endtask : sram_readword

  task automatic sram_writeword(
    const ref logic clk,

    ref sram_l2m_t       l2m,
    const ref logic      gnt,
    const ref sram_m2l_t m2l,

    input logic [SramAw-1:0] addr,
    input logic [SramDw-1:0] wdata
  );
    l2m.req   = 1'b 1;
    l2m.addr  = addr;
    l2m.we    = 1'b 1;
    l2m.wdata = wdata;
    l2m.wstrb = '1;

    @(posedge clk iff gnt == 1'b 1);
    l2m.req   = 1'b 0;

  endtask : sram_writeword

  /////////////////
  // TL-UL agent //
  /////////////////
  task automatic tlul_write(
    const ref logic clk,

    ref tlul_pkg::tl_h2d_t       h2d,
    const ref tlul_pkg::tl_d2h_t d2h,

    input logic [31:0] address,
    input logic [31:0] wdata,
    input logic [ 3:0] wstrb
  );

    // Assume always called this task @(posedge clk);
    h2d.a_valid   = 1'b 1;
    h2d.a_address = address;
    h2d.a_opcode  = tlul_pkg::PutFullData;
    h2d.a_data    = wdata;
    h2d.a_mask    = wstrb;
    h2d.a_param   = '0;
    h2d.a_size    = $clog2($countones(wstrb));
    h2d.a_source  = '0;

    h2d.d_ready   = 1'b 0;

    // Due to interity checker instance, `a_ready` from SW view is delayed.
    // Need to see the a_ready then wait posedge.
    // Previously: @(posedge clk iff d2h.a_ready);
    wait(d2h.a_ready);
    @(posedge clk);
    h2d.a_valid = 1'b 0;
    h2d.d_ready = 1'b 1;
    wait(d2h.d_valid);
    @(posedge clk);
    h2d.d_ready = 1'b 0;

  endtask : tlul_write

  task automatic tlul_read(
    const ref logic clk,

    ref tlul_pkg::tl_h2d_t       h2d,
    const ref tlul_pkg::tl_d2h_t d2h,

    input  logic [31:0] address,
    output logic [31:0] rdata
  );

    // Assume always called this task @(posedge clk);
    h2d.a_valid   = 1'b 1;
    h2d.a_address = address;
    h2d.a_opcode  = tlul_pkg::Get;
    h2d.a_data    = '0;
    h2d.a_mask    = '1;
    h2d.a_param   = '0;
    h2d.a_size    = 2;
    h2d.a_source  = '0;

    h2d.d_ready   = 1'b 0;

    wait(d2h.a_ready);
    @(posedge clk);
    h2d.a_valid = 1'b 0;
    h2d.d_ready = 1'b 1;
    wait(d2h.d_valid);
    @(posedge clk);
    rdata       = d2h.d_data;
    h2d.d_ready = 1'b 0;

  endtask : tlul_read

  task automatic tlul_rmw(
    const ref logic clk,

    ref tlul_pkg::tl_h2d_t       h2d,
    const ref tlul_pkg::tl_d2h_t d2h,

    input logic [31:0] address,
    input logic [31:0] data,
    input logic [31:0] mask
  );

    automatic logic [31:0] tl_data;

    tlul_read(clk, h2d, d2h, address, tl_data);
    tl_data = (tl_data & ~mask) | (mask & data);
    tlul_write(clk, h2d, d2h, address, tl_data, 4'b 1111);
  endtask : tlul_rmw

  // classes
  class SpiTrans;
    rand spi_device_pkg::spi_cmd_e cmd;
    rand bit                       addr_mode; // 1 : Addr4B, 0: Addr3B
    rand logic [31:0]              address;
    rand int unsigned              size;
    int unsigned                   dummy;
    mode_e                         io_mode;

    string str_cmd;

    function void post_randomize();
      str_cmd = cmd.name();
    endfunction : post_randomize

  endclass : SpiTrans

  class SpiTransWel extends SpiTrans;
    constraint wel_cmd_c {
      cmd inside {
        spi_device_pkg::CmdWriteDisable,
        spi_device_pkg::CmdWriteEnable
      };
      address   == 0;
      addr_mode == 0;
      size      == 0;
    };

    function void display();
      $display("SPI WREN/ WRDI Transaction:");
      $display("  Command: %s", str_cmd);
    endfunction : display
  endclass : SpiTransWel

  class SpiTransRead extends SpiTrans;
    // Information

    constraint read_cmd_c {
      cmd inside {spi_device_pkg::CmdReadData,
                  spi_device_pkg::CmdReadFast,
                  spi_device_pkg::CmdReadDual,
                  spi_device_pkg::CmdReadQuad
                  };
    }

    function void post_randomize();
      super.post_randomize();
      case (cmd)
        spi_device_pkg::CmdReadData: begin
          dummy = 0;
          io_mode = IoSingle;
        end
        spi_device_pkg::CmdReadFast: begin
          dummy = 8;
          io_mode = IoSingle;
        end
        spi_device_pkg::CmdReadDual: begin
          dummy = 4;
          io_mode = IoDual;
        end
        spi_device_pkg::CmdReadQuad: begin
          dummy = 3; // match with other pre_dv
          io_mode = IoQuad;
        end
        default: begin
          dummy = 8;
          io_mode = IoSingle;
        end
      endcase
    endfunction : post_randomize

    function automatic void display();
      $display("SPI Read Transaction:");
      $display("  Command: %s", str_cmd);
      $display("  Address: %8Xh Mode(%1d)", address, addr_mode);
      $display("  Size:    %4d",  size);
      $display("  Dummy:   %1d cycles", dummy);
      $display("");
    endfunction : display

  endclass : SpiTransRead

  class SpiTransProgram extends SpiTrans;
    rand bit wrap_test;
    rand spi_queue_t program_data;

    constraint pp_cmd_c { cmd == spi_device_pkg::CmdPageProgram;}

    // Up-to 256B, if over, it wraps around
    constraint size_c {
      if (wrap_test == 1'b 0) size >= 1 && size <= 256;
      else size > 256 && size <= 512;
    }

    constraint program_data_c {
      program_data.size() == size;
    }

    function automatic void display();
      automatic string payload_partial = ""; // to display first a few bytes
      automatic int unsigned bytes;

      bytes = $min(16, size) ;

      for (int i = 0 ; i < bytes ; i++) begin
        if (i == 0) payload_partial = $sformatf("%X", program_data[i]);
        else begin
          payload_partial = { payload_partial,
            " ",
            $sformatf("%X", program_data[i])
          };
        end
      end

      $display("SPI Page Program Transaction:");
      $display("  Address: %8Xh Mode(%1d)", address, addr_mode);
      $display("  Size:    %4d",  $min(256, size));
      $display("  Wrap Test: %1X", wrap_test);
      $display("  Payload: %s", payload_partial);
      $display("");
    endfunction : display
  endclass : SpiTransProgram

endpackage : spid_common
