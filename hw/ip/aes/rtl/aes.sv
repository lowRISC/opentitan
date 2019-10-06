// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES top-level wrapper

module aes #(
  parameter bit AES192Enable = 1
) (
  input                     clk_i,
  input                     rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  input                     devmode_i
);

  import aes_reg_pkg::*;

  aes_reg2hw_t reg2hw;
  aes_hw2reg_t hw2reg;

  aes_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .devmode_i
  );

  aes_core #(
    .AES192Enable (AES192Enable)
  ) aes_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg
  );

endmodule
