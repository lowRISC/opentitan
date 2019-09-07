// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Galois type LFSR ([1], internal XOR gates, very fast).
// Parameterizable width from 4 to 64 bits.
// Coefficients obtained from [2].
//
// Refs: [1] https://en.wikipedia.org/wiki/Linear-feedback_shift_register
//       [2] https://users.ece.cmu.edu/~koopman/lfsr/

module prim_lfsr #(
  // Lfsr width
  parameter int unsigned       LfsrDw = 32,
  // Width of input to be XOR'd into state (lfsr_q[InDw-1:0])
  parameter int unsigned       InDw   =  8,
  // Width of output tap (from lfsr_q[OutDw-1:0])
  parameter int unsigned       OutDw  =  8,
  // Lfsr reset state, must be nonzero!
  parameter logic [LfsrDw-1:0] Seed   = LfsrDw'(1),
  // Custom polynomial coeffs
  parameter logic [LfsrDw-1:0] Custom = '0
) (
  input                    clk_i,
  input                    rst_ni,
  input                    en_i,
  input        [InDw-1:0]  data_i,
  output logic [OutDw-1:0] data_o
);

  // automatically generated with get-lfsr-coeffs.py script
  localparam logic [63:0] coeffs [0:64]  = '{ 64'hx,
                                              64'hx,
                                              64'hx,
                                              64'hx,
                                              64'h9,
                                              64'h12,
                                              64'h21,
                                              64'h41,
                                              64'h8E,
                                              64'h108,
                                              64'h204,
                                              64'h402,
                                              64'h829,
                                              64'h100D,
                                              64'h2015,
                                              64'h4001,
                                              64'h8016,
                                              64'h10004,
                                              64'h20013,
                                              64'h40013,
                                              64'h80004,
                                              64'h100002,
                                              64'h200001,
                                              64'h400010,
                                              64'h80000D,
                                              64'h1000004,
                                              64'h2000023,
                                              64'h4000013,
                                              64'h8000004,
                                              64'h10000002,
                                              64'h20000029,
                                              64'h40000004,
                                              64'h80000057,
                                              64'h100000029,
                                              64'h200000073,
                                              64'h400000002,
                                              64'h80000003B,
                                              64'h100000001F,
                                              64'h2000000031,
                                              64'h4000000008,
                                              64'h800000001C,
                                              64'h10000000004,
                                              64'h2000000001F,
                                              64'h4000000002C,
                                              64'h80000000032,
                                              64'h10000000000D,
                                              64'h200000000097,
                                              64'h400000000010,
                                              64'h80000000005B,
                                              64'h1000000000038,
                                              64'h200000000000E,
                                              64'h4000000000025,
                                              64'h8000000000004,
                                              64'h10000000000023,
                                              64'h2000000000003E,
                                              64'h40000000000023,
                                              64'h8000000000004A,
                                              64'h100000000000016,
                                              64'h200000000000031,
                                              64'h40000000000003D,
                                              64'h800000000000001,
                                              64'h1000000000000013,
                                              64'h2000000000000034,
                                              64'h4000000000000001,
                                              64'h800000000000000D };

  logic [LfsrDw-1:0] lfsr_d, lfsr_q;

  // Custom Galois polynomial
  if (Custom) begin : gen_custom
    assign lfsr_d = (en_i) ? LfsrDw'(data_i) ^ ({LfsrDw{lfsr_q[0]}} &
                             Custom[LfsrDw-1:0]) ^ (lfsr_q >> 1)
                           : lfsr_q;
  end else begin : gen_lut
    assign lfsr_d = (en_i) ? LfsrDw'(data_i) ^ ({LfsrDw{lfsr_q[0]}} &
                             coeffs[LfsrDw][LfsrDw-1:0]) ^ (lfsr_q >> 1)
                           : lfsr_q;
  end

  assign data_o  = lfsr_q[OutDw-1:0];

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_reg
    if (!rst_ni) begin
      lfsr_q <= Seed;
    end else begin
      lfsr_q <= lfsr_d;
    end
  end

  // assertions
  `ASSERT_INIT(InputWidth, LfsrDw >= InDw)
  `ASSERT_INIT(OutputWidth, LfsrDw >= OutDw)
  `ASSERT_INIT(MinLfsrWidth, LfsrDw >= $low(coeffs))
  `ASSERT_INIT(MaxLfsrWidth, LfsrDw <= $high(coeffs))
  // check that the most significant bit of polynomial is 1
  `ASSERT_INIT(CoeffNzCheck, (Custom && Custom[LfsrDw-1]) ||
                             (!Custom) && coeffs[LfsrDw][LfsrDw-1])
  `ASSERT_INIT(SeedNzCheck, Seed)
  `ASSERT(LfsrNzCheck, lfsr_q, clk_i, !rst_ni)

endmodule
