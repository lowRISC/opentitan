// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Wrapper around the HPC3 AND gadget (prim_hpc3 with EnW=0) for side-channel
// analysis. Exposes a 2-bit combined input interface: bit 0 carries input A,
// bit 1 carries input B. Uses 2-bit randomness (r and rp). Used as the
// top-level module for Alma and PROLEAD leakage verification flows.

module prim_hpc3_sca_wrapper #(
  localparam int Width     = 2,
  localparam int RandWidth = 2,
  localparam int NumShares = 2
) (
  input clk_i,
  input rst_ni,

  input  logic                 en_i,
  input  logic [RandWidth-1:0] rand_i,
  input  logic [Width-1:0]     share0_i,
  input  logic [Width-1:0]     share1_i,
  output logic [NumShares-1:0] sum_o
);

  logic [NumShares-1:0] a_shares;
  logic [NumShares-1:0] b_shares;
  logic [NumShares-1:0] sum;

  // Extract shares for A and B from the combined share inputs.
  assign a_shares[0] = share0_i[0];
  assign a_shares[1] = share1_i[0];
  assign b_shares[0] = share0_i[1];
  assign b_shares[1] = share1_i[1];
  assign sum_o = sum;

  prim_hpc3 #(
    .EnW(1'b0)
  ) u_prim_hpc3 (
    .clk_i,
    .rst_ni,
    .en_i (en_i),
    .x_i  (a_shares),
    .y_i  (b_shares),
    .w_i  ('0),
    .r_i  (rand_i[0]),
    .rp_i (rand_i[1]),
    .z_o  (sum)
  );

endmodule : prim_hpc3_sca_wrapper
