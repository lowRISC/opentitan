// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module pwm #(
  parameter int NOutputs = 6
) (
  input                       clk_i,
  input                       rst_ni,

  input                       clk_core_i,
  input                       rst_core_ni,

  input                       tlul_pkg::tl_h2d_t tl_i,
  output                      tlul_pkg::tl_d2h_t tl_o,

  output logic [NOutputs-1:0] cio_pwm_o,
  output logic [NOutputs-1:0] cio_pwm_en_o
);

  // TODO: Deal with Regen in this block, on TLUL clock domain
  logic                     unused_regen;
  pwm_reg_pkg::pwm_reg2hw_t reg2hw;

  assign unused_regen = reg2hw.regen.q;

  pwm_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .intg_err_o (),
    .devmode_i  (1'b1)
  );

  assign cio_pwm_en_o = {NOutputs{1'b1}};

  pwm_core #(.NOutputs(NOutputs)) u_pwm_core (
    .clk_core_i,
    .rst_core_ni,
    .reg2hw,
    .pwm_o       (cio_pwm_o)
  );

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)

  `ASSERT_KNOWN(CioPWMKnownO_A, cio_pwm_o)

endmodule : pwm
