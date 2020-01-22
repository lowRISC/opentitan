// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src top level wrapper file

module entropy_src  #(
  parameter int unsigned EsFifoDepth = 32
) (
  input           clk_i,
  input           rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Interrupts
  output logic    es_entropy_valid_o,
  output logic    es_entropy_fifo_err_o
);

  import entropy_src_reg_pkg::*;

  entropy_src_reg2hw_t reg2hw;
  entropy_src_hw2reg_t hw2reg;

  entropy_src_reg_top u_entropy_src_reg_top (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,

    .devmode_i(1'b1)
  );

  entropy_src_core u_entropy_src_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .es_entropy_valid_o,
    .es_entropy_fifo_err_o
  );

endmodule
