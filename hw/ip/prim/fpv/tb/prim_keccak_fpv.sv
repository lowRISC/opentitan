// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_keccak. Intended to be used with a formal tool.

module prim_keccak_fpv #(
  parameter int Width = 1600
) (
  input                    clk_i,
  input                    rst_ni,
  input                    valid_i,
  input        [Width-1:0] state_i,
  output logic             done_o,
  output logic [Width-1:0] state_o
);

  localparam int W        = Width/25;
  localparam int L        = $clog2(W);
  localparam int NumRound = 12 + 2*L; // Keccak-f only
  localparam int RndW     = $clog2(NumRound+1);
  logic [RndW-1:0] round;
  logic active;
  logic [Width-1:0] state, state_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) state <= '0;
    else if (valid_i) state <= state_i;
    else if (active)  state <= state_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) round <= '0;
    else if (valid_i) round <= '0;
    else if (active)  round <= round + 1'b 1;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) active <= 1'b 0;
    else if (valid_i) active <= 1'b 1;
    else if (round == (NumRound -1)) active <= 1'b 0;
  end

  assign done_o = (round == NumRound);
  assign state_o = state;

  prim_keccak #(
    .Width (Width)
  ) u_keccak (
    .rnd_i  (round),
    .s_i    (state),
    .s_o    (state_d)
  );


  `ASSUME_FPV(ValidSequence_A, ##1 valid_i |=> !valid_i)
  `ASSUME_FPV(ValidValid_A, active |-> !valid_i)

  // Test with value 0
  logic [1599:0] data_0 ;
  always_comb begin
    data_0 = '0;
    // SHA3-256 ==> r : 1088
    data_0[1087] = 1'b 1;
    data_0[2:0] = 3'b 110;
  end
  logic [255:0] digest_0;
  // Big-Endian a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a
  assign digest_0 = 256'h 4a43_f880_4b0a_d882_fa49_3be4_4dff_80f5_62d6_61a0_5647_c151_66d7_1ebf_f8c6_ffa7;
  `ASSUME_FPV(Data0TestSHA3_256_A, state_i == data_0)
  `ASSERT(DigestForData0TestSHA3_256_A, done_o |-> state_o[255:0] == digest_0)

endmodule

