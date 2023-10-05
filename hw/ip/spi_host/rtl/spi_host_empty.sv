// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Host module.
//
//

`include "prim_assert.sv"

module spi_host_ot_empty
  import spi_host_reg_ot_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input              clk_i,
  input              rst_ni,

  // Register interface
  input              tlul_ot_pkg::tl_h2d_t tl_i,
  output             tlul_ot_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // SPI Interface
  output logic             cio_sck_o,
  output logic             cio_sck_en_o,
  output logic [NumCS-1:0] cio_csb_o,
  output logic [NumCS-1:0] cio_csb_en_o,
  output logic [3:0]       cio_sd_o,
  output logic [3:0]       cio_sd_en_o,
  input        [3:0]       cio_sd_i,

  // Passthrough interface
  input  spi_device_pkg::passthrough_req_t passthrough_i,
  output spi_device_pkg::passthrough_rsp_t passthrough_o,

  output logic             intr_error_o,
  output logic             intr_spi_event_o
);

   logic  unused;

   assign alert_tx_o = '0;
   assign tl_o = '0;

   assign cio_sck_o = 1'b0;
   assign cio_sck_en_o = 1'b0;
   assign cio_csb_o = '0;
   assign cio_csb_en_o = '0;
   assign cio_sd_o = '0;
   assign cio_sd_en_o = '0;

   assign intr_error_o = 1'b0;
   assign intr_spi_event_o = 1'b0;

   assign passthrough_o = '0;

   assign unused = ^passthrough_i & ^cio_sd_i & ^alert_rx_i & ^tl_i & clk_i & rst_ni;

endmodule
