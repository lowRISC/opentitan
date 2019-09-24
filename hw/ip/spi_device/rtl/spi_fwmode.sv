// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI FW Mode: Intention of this mode is to download FW image. Doesn't parse Commands
//

module spi_fwmode (
  // MOSI
  input clk_in_i,
  input rst_in_ni,

  // MISO
  input clk_out_i,
  input rst_out_ni,

  // Configurations
  // No sync logic. Configuration should be static when SPI operating
  input                             cpha_i,
  input                             cfg_rxorder_i, // 1: 0->7 , 0:7->0
  input                             cfg_txorder_i, // 1: 0->7 , 0:7->0
  input  spi_device_pkg::spi_mode_e mode_i, // Only works at mode_i == FwMode

  // RX, TX FIFO interface
  output logic                      rx_wvalid_o,
  input                             rx_wready_i,
  output spi_device_pkg::spi_byte_t rx_data_o,

  input                             tx_rvalid_i,
  output logic                      tx_rready_o,
  input  spi_device_pkg::spi_byte_t tx_data_i,

  output logic                      rx_overflow_o,
  output logic                      tx_underflow_o,

  // SPI Interface: clock is given (ckl_in_i, clk_out_i)
  input        csb_i,
  input        mosi,
  output logic miso,
  output logic miso_oe
);

  import spi_device_pkg::*;

  localparam int unsigned BITS     = $bits(spi_byte_t);
  localparam int unsigned BITWIDTH = $clog2(BITS);

  logic [BITWIDTH-1:0] rx_bitcount;

  typedef enum logic {
    TxIdle,
    TxActive
  } tx_state_e;
  tx_state_e tx_state;   // Only for handling CPHA

  spi_byte_t rx_data_d, rx_data_q;

  // Serial to Parallel
  always_comb begin
    if (cfg_rxorder_i) begin
      rx_data_d = {mosi, rx_data_q[BITS-1:1]};
    end else begin
      rx_data_d = {rx_data_q[BITS-2:0], mosi};
    end
  end

  always_ff @(posedge clk_in_i) begin
    rx_data_q <= rx_data_d;
  end

  // As SCK shut off right after bytes are transferred,
  // HW should give current MOSI and latched version of rx_data
  // if not, FIFO request should be generated next cycle but it cannot be (as no clock exist)
  // It means RX_FIFO should latch the write request at negedge of clk_in_i
  assign rx_data_o = rx_data_d;

  // Counter to generate write signal
  always_ff @(posedge clk_in_i or negedge rst_in_ni) begin
    if (!rst_in_ni) begin
      rx_bitcount <= BITWIDTH'(BITS-1);
    end else begin
      if (rx_bitcount == '0) begin
        rx_bitcount <= BITWIDTH'(BITS-1);
      end else begin
        rx_bitcount <= rx_bitcount -1;
      end
    end
  end

  assign rx_wvalid_o = (rx_bitcount == '0);

  // TX Serialize
  logic [BITWIDTH-1:0] tx_bitcount;
  logic first_bit, last_bit;
  spi_byte_t miso_shift;

  assign first_bit = (tx_bitcount == BITWIDTH'(BITS-1)) ? 1'b1 : 1'b0;
  assign last_bit  = (tx_bitcount == '0) ? 1'b1 : 1'b0;
  // Pop the entry from the FIFO at bit 1.
  //    This let the module pop the entry correctly when CPHA == 1 If CPHA is set, there is no clock
  //    posedge after bitcnt is 0 right before CSb is de-asserted.  So TX Async FIFO pop signal
  //    cannot be latched inside FIFO.  It is safe to pop between bitcnt 6 to 1. If pop signal is
  //    asserted when bitcnt 7 it can pop twice if CPHA is 1.
  assign tx_rready_o = (tx_bitcount == BITWIDTH'(1)); // Pop at second bit transfer
  always_ff @(posedge clk_out_i or negedge rst_out_ni) begin
    if (!rst_out_ni) begin
      tx_bitcount <= BITWIDTH'(BITS-1);
    end else begin
      if (last_bit) begin
        tx_bitcount <= BITWIDTH'(BITS-1);
      end else if (tx_state != TxIdle || cpha_i == 1'b0) begin
        tx_bitcount <= tx_bitcount - 1'b1;
      end
    end
  end
  always_ff @(posedge clk_out_i or negedge rst_out_ni) begin
    if (!rst_out_ni) begin
      tx_state <= TxIdle;
    end else begin
      tx_state <= TxActive;
    end
  end

  assign miso = (cfg_txorder_i) ? ((~first_bit) ? miso_shift[0] : tx_data_i[0]) :
                (~first_bit) ? miso_shift[7] : tx_data_i[7] ;
  assign miso_oe = ~csb_i;

  always_ff @(posedge clk_out_i) begin
    if (cfg_txorder_i) begin
      if (first_bit) begin
        miso_shift <= {1'b0, tx_data_i[7:1]};
      end else begin
        miso_shift <= {1'b0, miso_shift[7:1]};
      end
    end else begin
      if (first_bit) begin
        // Dummy byte cannot be used. empty signal could be delayed two clocks to cross
        // async clock domain. It means even FW writes value to FIFO, empty signal deasserts
        // after two negative edge of SCK. HW module already in the middle of sending DUMMY.
        miso_shift <= {tx_data_i[6:0], 1'b0};
      end else begin
        miso_shift <= {miso_shift[6:0], 1'b0};
      end
    end
  end

  // Events: rx_overflow, tx_underflow
  //    Reminder: Those events are not 100% accurate. If the event happens at
  //    the end of the transaction right before CSb de-assertion, the event
  //    cannot be propagated to the main clock domain due to the reset and lack
  //    of SCK after CSb de-assertion.
  //
  //    For these events to be propagated to the main clock domain, it needds
  //    one more clock edge to creates toggle signal in the pulse synchronizer.
  assign rx_overflow_o  = rx_wvalid_o & ~rx_wready_i;
  assign tx_underflow_o = tx_rready_o & ~tx_rvalid_i;

endmodule
