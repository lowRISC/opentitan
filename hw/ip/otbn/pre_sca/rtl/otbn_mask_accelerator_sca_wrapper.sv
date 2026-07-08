// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// SCA wrapper for otbn_mask_accelerator. Accepts all SecAddVecSize elements at once as flat input
// buses and serializes them one per cycle into the DUT.

module otbn_mask_accelerator_sca_wrapper
  import otbn_pkg::*;
#(
  parameter  int Width          = SecAddWidth,
  localparam int RandWidth      = SecAddRandWidth(Width),
  localparam int DoubleWidth    = 2 * Width,
  localparam int TotalRandWidth = RandWidth + DoubleWidth,
  localparam int FlatShareWidth = SecAddVecSize * DoubleWidth,
  localparam int CtrWidth       = $clog2(SecAddVecSize)
) (
  input  logic clk_i,
  input  logic rst_ni,

  // rand_i = {mask1, mask0, adder_rand}: [RandWidth-1:0] adder randomness,
  //          [TotalRandWidth-1:RandWidth] arithmetic masks.
  input  logic [TotalRandWidth-1:0]        rand_i,
  input  logic [Width-1:0]                 mod_i,
  input  mask_op_e                         mask_op_i,

  // All SecAddVecSize elements presented at once; serialized internally.
  // share{0,1}_i[k*DoubleWidth +: Width]         = in0_share{0,1}[k]
  // share{0,1}_i[k*DoubleWidth + Width +: Width] = in1_share{0,1}[k]
  input  logic [FlatShareWidth-1:0]        share0_i,
  input  logic [FlatShareWidth-1:0]        share1_i,
  input  logic                             en_i,
  input  logic                             sec_wipe_running_i,
  input  logic                             rready_i,

  output logic [NumShares-1:0][Width-1:0]  result_o,
  output logic                             rvalid_o
);

  logic [CtrWidth-1:0] ctr_q;
  logic                done_q;
  logic                wready;

  // Advance the counter on each accepted input; latch done after VecSize elements.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ctr_q  <= '0;
      done_q <= 1'b0;
    end else if (en_i && !done_q && wready) begin
      if (ctr_q == CtrWidth'(SecAddVecSize - 1)) begin
        ctr_q  <= '0;
        done_q <= 1'b1;
      end else begin
        ctr_q <= ctr_q + 1'b1;
      end
    end
  end

  // Hold wvalid high until all elements have been accepted.
  logic wvalid;
  assign wvalid = en_i && !done_q;

  // Mux the current element from the flat share buses.
  logic [NumShares-1:0][Width-1:0] in0_shares, in1_shares;
  always_comb begin
    in0_shares[0] = share0_i[ctr_q * DoubleWidth +: Width];
    in0_shares[1] = share1_i[ctr_q * DoubleWidth +: Width];
    in1_shares[0] = share0_i[ctr_q * DoubleWidth + Width +: Width];
    in1_shares[1] = share1_i[ctr_q * DoubleWidth + Width +: Width];
  end

  // Arithmetic masks extracted from the upper part of rand_i.
  logic [NumShares-1:0][Width-1:0] remask_rand;
  assign remask_rand[0] = rand_i[RandWidth +: Width];
  assign remask_rand[1] = rand_i[RandWidth + Width +: Width];

  otbn_mask_accelerator #(
    .EnRejSampling(1'b0)
  ) u_otbn_mask_accelerator (
    .clk_i,
    .rst_ni,
    .sec_wipe_running_i,
    .wvalid_i          (wvalid),
    .wready_o          (wready),
    .in0_i             (in0_shares),
    .in1_i             (in1_shares),
    .rand_i            (rand_i[RandWidth-1:0]),
    .remask_rand_i     (remask_rand),
    .mod_i,
    .mask_op_i,
    .rvalid_o,
    .rready_i,
    .result_o,
    .mask_fifo_err_o   (),
    .ctr_err_o         ()
  );

endmodule : otbn_mask_accelerator_sca_wrapper
