// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_mask_accelerator_sca_wrapper_prolead
  import otbn_pkg::*;
#(
  parameter  int Width          = SecAddWidth,
  localparam int RandWidth      = SecAddRandWidth(Width),
  localparam int DoubleWidth    = 2*Width,
  localparam int TotalRandWidth = RandWidth + DoubleWidth
) (
  input  logic clk_i,
  input  logic rst_ni,

  input  logic wvalid_i,
  output logic rvalid_o,

  // rand_i = {mask1, mask0, adder_rand}:
  //    [RandWidth-1:0]              adder randomness,
  //    [TotalRandWidth-1:RandWidth] arithmetic masks.
  input  logic [TotalRandWidth-1:0]        rand_i,
  input  logic [Width-1:0]                 mod_i,
  input  mask_op_e                         mask_op_i,

  // share0_i = {b_share0, a_share0}
  input  logic [DoubleWidth-1:0]           share0_i,
  // share1_i = {b_share1, a_share1}
  input  logic [DoubleWidth-1:0]           share1_i,

  output logic [NumShares-1:0][Width-1:0]  result_o,
  output logic                             mask_fifo_err_o,
  output logic                             ctr_err_o
);

  logic [NumShares-1:0][Width-1:0] in0_shares;
  logic [NumShares-1:0][Width-1:0] in1_shares;
  logic [NumShares-1:0][Width-1:0] remask_rand;

  assign remask_rand[0] = rand_i[RandWidth +: Width];
  assign remask_rand[1] = rand_i[RandWidth + Width +: Width];

  assign in0_shares[0] = share0_i[Width-1:0];
  assign in0_shares[1] = share1_i[Width-1:0];
  assign in1_shares[0] = share0_i[DoubleWidth-1:Width];
  assign in1_shares[1] = share1_i[DoubleWidth-1:Width];

  otbn_mask_accelerator #(
    .Width        (Width),
    .EnRejSampling(1'b0)
  ) u_otbn_mask_accelerator (
    .clk_i,
    .rst_ni,
    .sec_wipe_running_i(1'b0),
    .wvalid_i,
    .wready_o          (),
    .in0_i             (in0_shares),
    .in1_i             (in1_shares),
    .rand_i            (rand_i[RandWidth-1:0]),
    .remask_rand_i     (remask_rand),
    .mod_i,
    .mask_op_i,
    .rvalid_o,
    .rready_i          (1'b1),
    .result_o,
    .mask_fifo_err_o,
    .ctr_err_o
  );

endmodule : otbn_mask_accelerator_sca_wrapper
