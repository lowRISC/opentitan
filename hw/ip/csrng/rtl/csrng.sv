// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng top level wrapper file

module csrng import csrng_pkg::*; import entropy_src_pkg::*; #(
  parameter int unsigned NHwApps = 3
) (
  input logic         clk_i,
  input logic         rst_ni,

  // Tilelink Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Efuse Interface
  input efuse_sw_app_enable_i,

  // Entropy Interface
  output entropy_src_hw_if_req_t entropy_src_hw_if_o,
  input  entropy_src_hw_if_rsp_t entropy_src_hw_if_i,

  // Application Interfaces
  input  csrng_req_t  [NHwApps:1] csrng_cmd_i,
  output csrng_rsp_t  [NHwApps:1] csrng_cmd_o,

  // Interrupts
  output logic    cs_cmd_req_done_o,
  output logic    cs_fifo_err_o
);


  import csrng_reg_pkg::*;

  csrng_reg2hw_t reg2hw;
  csrng_hw2reg_t hw2reg;

  csrng_reg_top u_csrng_reg_top (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,

    .devmode_i(1'b1)
  );

  csrng_core
    #(.NHwApps(NHwApps))
      u_csrng_core
        (
         .clk_i,
         .rst_ni,
         .reg2hw,
         .hw2reg,

         .efuse_sw_app_enable_i,
         // Entropy Interface
         .entropy_src_hw_if_o,
         .entropy_src_hw_if_i,

         // Application Interfaces
         .csrng_cmd_i,
         .csrng_cmd_o,

         .cs_cmd_req_done_o,
         .cs_fifo_err_o
         );

endmodule
