// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES KeyExpand

module aes_key_expand #(
  parameter bit AES192Enable = 1
) (
  input  logic           clk_i,
  input  logic           rst_ni,
  input  aes_pkg::mode_e mode_i,
  input  logic           clear_i,
  input  logic [31:0]    key_i [8],
  output logic [31:0]    key_o [8]
);

import aes_pkg::*;

// dummy only
logic  unused_clk;
logic  unused_rst_n;
mode_e unused_mode;
logic  unused_clear;
assign unused_clk   = clk_i;
assign unused_rst_n = rst_ni;
assign unused_mode  = mode_i;
assign unused_clear = clear_i;
assign key_o        = key_i;

endmodule
