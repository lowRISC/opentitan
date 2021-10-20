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

// spid_common package contains common tasks, functions
package spid_common;
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

  // spi_transaction: Send/ Receive data using data fifo.
  task automatic spi_transaction(
    virtual spi_if.tb sif,
    ref spi_fifo_t d_in  [$],
    ref spi_data_t d_out [$]
  );
    automatic spi_data_t char;
    automatic mode_e     mode;
    automatic dir_e      dir;
    automatic spi_data_t rcv_byte;

    // Assert CSb
    spi_start(sif);

    // pop data from `d_in[$]`
    foreach (d_in[i]) begin
      $display("Popped from d_in[%d]: %x", i, d_in[i].data);

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
          // High-Z Explicit float and wait a byte
          spi_highz(sif, mode);
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

    $display("SPI Byte sent!: %x", data);
  endtask: spi_sendbyte

  task automatic spi_highz(virtual spi_if.tb sif, input mode_e mode);
    automatic int unsigned loop;

    sif.sd_in[3:0] = 4'h z;

    loop = (mode == IoSingle) ? 7 :
           (mode == IoDual)   ? 3 :
           (mode == IoQuad)   ? 1 : 7;
    repeat(loop) @(negedge sif.clk);
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

    $display("SPI Byte Sent/Received!: %x / %x", send_byte, rcv_byte);

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

    $display("SPI Byte Received: %x", rcv_byte);

    // Always end with negative edge to complete the byte
    @(negedge sif.clk);

  endtask : spi_receivebyte

  ////////////////////////
  // SPI Flash Commands //
  ////////////////////////
  task automatic spiflash_readstatus(
    virtual spi_if.tb sif,
    input spi_data_t  opcode,
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

  task automatic spiflash_readjedec(
    virtual spi_if.tb  sif,
    input spi_data_t   opcode,
    ref   logic [23:0] jedec_id // [23:16] Manufacurer ID, [15:0] ID
  );
    automatic spi_fifo_t send_data [$];
    automatic spi_data_t rcv_data  [$];

    assert(opcode == 8'h 9F);

    send_data.push_back('{data: opcode, dir: DirIn,  mode: IoSingle});

    // Receive 3 bytes from DUT
    repeat (3) begin
      send_data.push_back('{data: '0, dir: DirOut, mode: IoNone});
    end

    spi_transaction(sif, send_data, rcv_data);

    assert(rcv_data.size() == 3);

    jedec_id[23:16] = rcv_data.pop_front();
    jedec_id[15:8]  = rcv_data.pop_front();
    jedec_id[7:0]   = rcv_data.pop_front();

    $display("Jedec ID Received: Manufacturer ID [%x], JEDEC_ID [%x]",
      jedec_id[23:16], jedec_id[15:0]);

  endtask : spiflash_readjedec

endpackage : spid_common
