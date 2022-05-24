// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface spi_passthrough_if
(
  input rst_n
);

  bit       passthrough_en;
  bit       sck;
  bit       sck_en;
  bit       csb;
  bit       csb_en;
  bit [3:0] is;
  bit [3:0] os;
  bit [3:0] s_en;
  bit       cio_sck_o;
  bit       cio_sck_en_o;
  bit       cio_csb_o;
  bit       cio_csb_en_o;
  bit [3:0] cio_sd_o;
  bit [3:0] cio_sd_en_o;
  bit [3:0] cio_sd_i;

endinterface : spi_passthrough_if
