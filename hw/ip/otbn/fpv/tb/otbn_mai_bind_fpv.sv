// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module otbn_mai_bind_fpv;


  bind otbn_mai otbn_mai_assert_fpv #(
    .SecFixMaiOpSeq(SecFixMaiOpSeq)
  ) i_otbn_mai_assert_fpv (
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


endmodule : otbn_mai_bind_fpv
