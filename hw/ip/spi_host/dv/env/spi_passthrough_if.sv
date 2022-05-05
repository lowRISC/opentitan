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
  logic [3:0]   cio_sd_o;
  bit [3:0]   cio_sd_i;

endinterface : spi_passthrough_if
