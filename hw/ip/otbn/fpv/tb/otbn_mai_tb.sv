// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for otbn_mai.
// Intended to be used with a formal tool.

module otbn_mai_tb
  import otbn_pkg::*;
#(
  parameter bit SecFixMaiOpSeq = 1'b0
) (
  input logic clk_i,
  input logic rst_ni,
  input logic sec_wipe_mai_i,
  input logic sec_wipe_running_i,
  input logic ispr_mai_ctrl_wr_i,
  input logic[31:0] ispr_mai_ctrl_wdata_i,
  output logic[31:0] ispr_mai_ctrl_rdata_o,
  output logic[31:0] ispr_mai_status_rdata_o,
  input logic ispr_mai_in0_s0_wr_i,
  input logic sec_wipe_ispr_mai_in0_s0_i,
  input logic[ExtWLEN-1:0] ispr_mai_in0_s0_wdata_i,
  input logic ispr_mai_in0_s1_wr_i,
  input logic sec_wipe_ispr_mai_in0_s1_i,
  input logic[ExtWLEN-1:0] ispr_mai_in0_s1_wdata_i,
  input logic ispr_mai_in1_s0_wr_i,
  input logic sec_wipe_ispr_mai_in1_s0_i,
  input logic[ExtWLEN-1:0] ispr_mai_in1_s0_wdata_i,
  input logic ispr_mai_in1_s1_wr_i,
  input logic sec_wipe_ispr_mai_in1_s1_i,
  input logic[ExtWLEN-1:0] ispr_mai_in1_s1_wdata_i,
  input logic ispr_mai_res_s0_wr_i,
  input logic sec_wipe_ispr_mai_res_s0_i,
  input logic[ExtWLEN-1:0] ispr_mai_res_s0_wdata_i,
  input logic ispr_mai_res_s1_wr_i,
  input logic sec_wipe_ispr_mai_res_s1_i,
  input logic[ExtWLEN-1:0] ispr_mai_res_s1_wdata_i,
  output logic[ExtWLEN-1:0] ispr_mai_in0_s0_rdata_o,
  output logic[ExtWLEN-1:0] ispr_mai_in0_s1_rdata_o,
  output logic[ExtWLEN-1:0] ispr_mai_in1_s0_rdata_o,
  output logic[ExtWLEN-1:0] ispr_mai_in1_s1_rdata_o,
  output logic[ExtWLEN-1:0] ispr_mai_res_s0_rdata_o,
  output logic[ExtWLEN-1:0] ispr_mai_res_s1_rdata_o,
  input logic[ExtWLEN-1:0] ispr_mod_intg_i,
  output logic mai_software_error_o,
  output logic mai_reg_intg_violation_err_o,
  output logic mai_state_err_o,
  input logic[UrndLen-1:0] urnd_data_i
);


  otbn_mai #(
    .SecFixMaiOpSeq(SecFixMaiOpSeq)
  ) dut (
    .clk_i,
    .rst_ni,
    .sec_wipe_mai_i,
    .sec_wipe_running_i,
    .ispr_mai_ctrl_wr_i,
    .ispr_mai_ctrl_wdata_i,
    .ispr_mai_ctrl_rdata_o,
    .ispr_mai_status_rdata_o,
    .ispr_mai_in0_s0_wr_i,
    .sec_wipe_ispr_mai_in0_s0_i,
    .ispr_mai_in0_s0_wdata_i,
    .ispr_mai_in0_s1_wr_i,
    .sec_wipe_ispr_mai_in0_s1_i,
    .ispr_mai_in0_s1_wdata_i,
    .ispr_mai_in1_s0_wr_i,
    .sec_wipe_ispr_mai_in1_s0_i,
    .ispr_mai_in1_s0_wdata_i,
    .ispr_mai_in1_s1_wr_i,
    .sec_wipe_ispr_mai_in1_s1_i,
    .ispr_mai_in1_s1_wdata_i,
    .ispr_mai_res_s0_wr_i,
    .sec_wipe_ispr_mai_res_s0_i,
    .ispr_mai_res_s0_wdata_i,
    .ispr_mai_res_s1_wr_i,
    .sec_wipe_ispr_mai_res_s1_i,
    .ispr_mai_res_s1_wdata_i,
    .ispr_mai_in0_s0_rdata_o,
    .ispr_mai_in0_s1_rdata_o,
    .ispr_mai_in1_s0_rdata_o,
    .ispr_mai_in1_s1_rdata_o,
    .ispr_mai_res_s0_rdata_o,
    .ispr_mai_res_s1_rdata_o,
    .ispr_mod_intg_i,
    .mai_software_error_o,
    .mai_reg_intg_violation_err_o,
    .mai_state_err_o,
    .urnd_data_i
  );


endmodule : otbn_mai_tb
