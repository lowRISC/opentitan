// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Host module.
//
//

`include "prim_assert.sv"

module spi_host (
  input clk_i,
  input rst_ni,

  input lc_ctrl_pkg::lc_tx_t scanmode_i,

  // Register interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // SPI Interface
  output logic       cio_sck_o,
  output logic       cio_sck_en_o,
  output logic       cio_csb_o,
  output logic       cio_csb_en_o,
  output logic [3:0] cio_sd_o,
  output logic [3:0] cio_sd_en_o,
  input        [3:0] cio_sd_i
);

  import spi_host_reg_pkg::*;

  spi_host_reg2hw_t reg2hw;
  spi_host_hw2reg_t hw2reg;

  // Register module
  spi_host_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i (tl_i),
    .tl_o (tl_o),

    .reg2hw,
    .hw2reg,

    .devmode_i  (1'b1)
  );

  // Some dummy connections
  assign cio_sd_o    = (reg2hw.control.dir.q) ? reg2hw.control.data.q : '0;
  assign cio_sd_en_o = (reg2hw.control.dir.q) ? reg2hw.control.data.q : '0;
  assign hw2reg.control.data.d  = (!reg2hw.control.dir.q) ? cio_sd_i : '0;
  assign hw2reg.control.data.de = (!reg2hw.control.dir.q) ? 1'b1 : 1'b0;

  assign cio_sck_o    = reg2hw.control.sck.q;
  assign cio_sck_en_o = reg2hw.control.sck.q;
  assign cio_csb_o    = reg2hw.control.csb.q;
  assign cio_csb_en_o = reg2hw.control.csb.q;

  logic unused_sigs;
  assign unused_sigs = ^scanmode_i;

  // Tie offs
  assign hw2reg.control.dir.d  = 1'b0;
  assign hw2reg.control.dir.de = 1'b0;
  assign hw2reg.control.sck.d  = 1'b0;
  assign hw2reg.control.sck.de = 1'b0;
  assign hw2reg.control.csb.d  = 1'b0;
  assign hw2reg.control.csb.de = 1'b0;

endmodule : spi_host
