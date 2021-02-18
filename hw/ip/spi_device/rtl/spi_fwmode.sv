// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI FW Mode: Intention of this mode is to download FW image. Doesn't parse Commands
//

module spi_fwmode
  import spi_device_pkg::*;
(
  // Configurations
  // No sync logic. Configuration should be static when SPI operating
  input  spi_mode_e mode_i, // Only works at mode_i == FwMode

  // RX, TX FIFO interface
  output logic      rx_wvalid_o,
  input             rx_wready_i,
  output spi_byte_t rx_data_o,

  input             tx_rvalid_i,
  output logic      tx_rready_o,
  input  spi_byte_t tx_data_i,

  output logic      rx_overflow_o,
  output logic      tx_underflow_o,

  // Serial to Parallel
  input             rx_data_valid_i,
  input  spi_byte_t rx_data_i,
  output io_mode_e  io_mode_o,

  // Parallel to SPI
  output logic      tx_wvalid_o,
  output spi_byte_t tx_data_o,
  input             tx_wready_i

);

  import spi_device_pkg::*;

  assign rx_wvalid_o = rx_data_valid_i;
  assign rx_data_o   = rx_data_i;

  assign tx_wvalid_o = 1'b 1;
  assign tx_rready_o = tx_wready_i;
  assign tx_data_o   = tx_data_i;

  // Generic Mode only uses SingleIO. s_i[0] is MOSI, s_o[1] is MISO.
  assign io_mode_o = SingleIO;

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
