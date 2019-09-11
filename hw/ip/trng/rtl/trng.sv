// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: TRNG top level wrapper file

module trng (
  input           clk_i,
  input           rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Interrupts
  output logic    intr_no_random_num_o,
  output logic    intr_stub_err_o
);

  import trng_reg_pkg::*;

  trng_reg2hw_t reg2hw;
  trng_hw2reg_t hw2reg;

  trng_reg_top u_trng_reg_top (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg
  );

  trng_core u_trng_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .intr_no_random_num_o,
    .intr_stub_err_o
  );

endmodule
