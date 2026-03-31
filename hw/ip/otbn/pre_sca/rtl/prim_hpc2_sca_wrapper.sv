// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Wrapper around the HPC2 AND gadget (prim_hpc2 with EnW=0) for side-channel
// analysis. Exposes a 2-bit combined input interface: bit 0 carries input A,
// bit 1 carries input B. Used as the top-level module for Alma and PROLEAD
// leakage verification flows.

module prim_hpc2_sca_wrapper #(
  localparam int Width     = 2,
  localparam int NumShares = 2
) (
  input clk_i,
  input rst_ni,

  input  logic en_i,
  input  logic rand_i,
  input  logic [Width-1:0] share0_i,
  input  logic [Width-1:0] share1_i,
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

  // Align x and en with HPC2's 2-cycle pipeline.
  logic [NumShares-1:0] a_q;
  prim_flop #(
    .Width(NumShares),
    .ResetValue('0)
  ) u_prim_flop_a (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .d_i   (a_shares),
    .q_o   (a_q)
  );

  logic en_q;
  prim_flop #(
    .Width(1),
    .ResetValue('0)
  ) u_prim_flop_en (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .d_i   (en_i),
    .q_o   (en_q)
  );

  prim_hpc2 #(
    .EnW(1'b0)
  ) u_prim_hpc2 (
    .clk_i,
    .rst_ni,
    .en1_i(en_i),
    .en2_i(en_q),
    .x_i  (a_q),
    .y_i  (b_shares),
    .w_i  ('0),
    .r_i  (rand_i),
    .z_o  (sum)
  );

endmodule : prim_hpc2_sca_wrapper
