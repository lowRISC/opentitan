// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for otbn_mai.
// Intended to be used with a formal tool.

`include "prim_assert.sv"

module otbn_mai_assert_fpv
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
  input logic[31:0] ispr_mai_ctrl_rdata_o,
  input logic[31:0] ispr_mai_status_rdata_o,
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
  input logic[ExtWLEN-1:0] ispr_mai_in0_s0_rdata_o,
  input logic[ExtWLEN-1:0] ispr_mai_in0_s1_rdata_o,
  input logic[ExtWLEN-1:0] ispr_mai_in1_s0_rdata_o,
  input logic[ExtWLEN-1:0] ispr_mai_in1_s1_rdata_o,
  input logic[ExtWLEN-1:0] ispr_mai_res_s0_rdata_o,
  input logic[ExtWLEN-1:0] ispr_mai_res_s1_rdata_o,
  input logic[ExtWLEN-1:0] ispr_mod_intg_i,
  input logic mai_software_error_o,
  input logic mai_reg_intg_violation_err_o,
  input logic mai_state_err_o,
  input logic[UrndLen-1:0] urnd_data_i
);

  ///////////////////////////////
  // Declarations & Parameters //
  ///////////////////////////////

  logic mai_busy = ispr_mai_status_rdata_o[0];
  logic mai_ready = ispr_mai_status_rdata_o[1];
  logic[4:0] mai_operation = ispr_mai_ctrl_wdata_i[5:1];
  /////////////////
  // Assumptions //
  /////////////////

  // `ASSUME(MyAssumption_M, ...)

  ////////////////////////
  // Forward Assertions //
  ////////////////////////

  // `ASSERT(MyFwdAssertion_A, ...)

  // Assert that the reserved bits of the MAI status register are always zero
  `ASSERT(MaiStatusRsvdBitsZero_A, ispr_mai_status_rdata_o[31:2] == 0)

  // Error Handling Assertions //
  // 
  // TODO: For the following assertions, should we be checking for $rose(mai_software_error_o) instead?
  // Assert that an OTBN software error is raised when a MAI operation is started while the MAI is busy
  `ASSERT(SwErrorFromStartWhileBusy, ispr_mai_ctrl_wr_i && ispr_mai_ctrl_wdata_i[0] == 1'b1 && mai_busy |=> mai_software_error_o == 1'b1)

  // Assert that an OTBN software error is raised when a MAI operation is started with an invalid operation value
  `ASSERT(SwErrorInvldOpVals_A, ispr_mai_ctrl_wr_i && mai_operation != 5'd11 && mai_operation != 5'd16 && mai_operation != 5'd23 && mai_operation != 5'd12 |=> mai_software_error_o == 1'b1)

  // Assert that an OTBN software error is raised when a MAI operation is set while the MAI is busy - TODO: Is this assertion checking the right thing? For when operation field is written to while MAI is busy?
  `ASSERT(SwErrorFromOpWrWhileBusy, ispr_mai_ctrl_wr_i && mai_operation != 5'd0 && mai_busy == 1'b1 |=> mai_software_error_o == 1'b1)

  // Assert that an OTBN software error is raised when a MAI operation is raised
  // when a write to MAI_INx_Sy is detected when the MAI is not ready

  `ASSERT(SwErrorFromInWeWhileNotReady, (ispr_mai_in0_s0_wr_i || ispr_mai_in0_s1_wr_i || ispr_mai_in1_s0_wr_i || ispr_mai_in1_s1_wr_i) && !mai_ready |=> mai_software_error_o == 1'b1)
  
  // TODO: Include error handling assertions for the other error signals (mai_reg_intg_violation_err_o and mai_state_err_o) when they are raised


  // Backward Assertions //
  /////////////////////////

  // `ASSERT(MyBkwdAssertion_A, ...)

  // Cover Properties go here

  // `COVER(name, prop, clk, rst)

  // Cover that the MAI status register indicates busy
  `COVER(mai_status_is_busy, mai_busy, clk_i, !rst_ni)

  // Cover that the MAI status register indicates not busy
  `COVER(mai_status_is_not_busy, !mai_busy, clk_i, !rst_ni)

  // Cover that the MAI status register indicates ready
  `COVER(mai_status_is_ready, mai_ready, clk_i, !rst_ni)

  // Cover that the MAI status register indicates not ready
  `COVER(mai_status_is_not_ready, !mai_ready, clk_i, !rst_ni)

  // Cover that the MAI status register indicates busy and ready at the same time
  `COVER(mai_status_is_busy_and_ready, mai_busy && mai_ready, clk_i, !rst_ni)

  // Cover that a MAI software error is raised
  // TODO: Should this be $rose(mai_software_error_o) instead?
  `COVER(mai_sw_err_seen, mai_software_error_o, clk_i, !rst_ni)
  
  // Cover that a MAI register integrity violation error is raised
  // TODO: Should this be $rose(mai_reg_intg_violation_err_o) instead?
  `COVER(mai_reg_intg_violation_seen, mai_reg_intg_violation_err_o, clk_i, !rst_ni)

  // Cover that a MAI state error is raised
  // TODO: Should this be $rose(mai_state_err_o) instead?
  `COVER(mai_state_err_seen, mai_state_err_o, clk_i, !rst_ni)


endmodule : otbn_mai_assert_fpv
