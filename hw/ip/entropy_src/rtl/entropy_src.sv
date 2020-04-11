// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src top level wrapper file


module entropy_src import entropy_src_pkg::*; #(
  parameter int unsigned EsFifoDepth = 32
) (
  input  clk_i,
  input  rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Efuse Interface
  input efuse_cs_sw_reg_en_i,

  // Entropy Interface
  input  entropy_src_hw_if_req_t entropy_src_hw_if_i,
  output entropy_src_hw_if_rsp_t entropy_src_hw_if_o,

  // Analog Interface
  input clk_es_50mhz_i,
  input rst_es_50mhz_ni,
  output es_mg_enable_o,
  input mg_es_ok_i,
  input [7:0] mg_bits_p_i,
  input [7:0] mg_bits_n_i,

  // Interrupts
  output logic    es_entropy_valid_o,
  output logic    es_ana_src_ok_o,
  output logic    es_ana_bits_err_o,
  output logic    es_ana_fifo_err_o,
  output logic    es_fifo_err_o
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

  entropy_src_core #(
    .EsFifoDepth(EsFifoDepth)
  ) u_entropy_src_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .efuse_cs_sw_reg_en_i,

    .entropy_src_hw_if_o,
    .entropy_src_hw_if_i,

    .clk_es_50mhz_i,
    .rst_es_50mhz_ni,
    .es_mg_enable_o,
    .mg_es_ok_i,
    .mg_bits_p_i,
    .mg_bits_n_i,

    .es_entropy_valid_o,
    .es_ana_src_ok_o,
    .es_ana_bits_err_o,
    .es_ana_fifo_err_o,
    .es_fifo_err_o
  );

endmodule
