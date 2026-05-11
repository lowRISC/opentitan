// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_sec_add_sca_wrapper #(
  parameter  int Width       = 32,
  localparam int NumShares   = 2,
  localparam int Stages      = $clog2(Width),
  localparam int RandWidth   = 2*(Stages*Width + 1),
  localparam int DoubleWidth = 2*Width
) (
  input clk_i,
  input rst_ni,

  input  logic                          en_i,
  input  logic [RandWidth-1:0]          rand_i,
  // share0_i = {b_share0, a_share0}, share1_i = {b_share1, a_share1}
  input  logic [DoubleWidth-1:0]        share0_i,
  input  logic [DoubleWidth-1:0]        share1_i,

  output logic [NumShares-1:0][Width:0] result_o,
  output logic                          valid_o
);

  logic [NumShares-1:0][Width-1:0] inp1_shares;
  logic [NumShares-1:0][Width-1:0] inp2_shares;

  assign inp1_shares[0] = share0_i[Width-1:0];
  assign inp1_shares[1] = share1_i[Width-1:0];
  assign inp2_shares[0] = share0_i[DoubleWidth-1:Width];
  assign inp2_shares[1] = share1_i[DoubleWidth-1:Width];

  otbn_sec_add u_otbn_sec_add (
    .clk_i,
    .rst_ni,
    .valid_i  (en_i),
    .stall_i  (1'b0),
    .rand_i   (rand_i),
    .inp1_i   (inp1_shares),
    .inp2_i   (inp2_shares),
    .result_o (result_o),
    .valid_o  (valid_o)
  );

endmodule : otbn_sec_add_sca_wrapper
