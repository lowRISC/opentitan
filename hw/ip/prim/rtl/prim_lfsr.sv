// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module implements different LFSR types:
//
// 0) Galois XOR type LFSR ([1], internal XOR gates, very fast).
//    Parameterizable width from 4 to 64 bits.
//    Coefficients obtained from [2].
//
// 1) Fibonacci XNOR type LFSR, parameterizable from 3 to 168 bits.
//    Coefficients obtained from [3].
//
// All flavors have an additional entropy input and lockup protection, which
// reseeds the state once it has accidentally fallen into the all-zero (XOR) or
// all-one (XNOR) state.
//
// All polynomials up to 34 bit in length have been verified in simulation.
//
// Refs: [1] https://en.wikipedia.org/wiki/Linear-feedback_shift_register
//       [2] https://users.ece.cmu.edu/~koopman/lfsr/
//       [3] https://www.xilinx.com/support/documentation/application_notes/xapp052.pdf

module prim_lfsr #(
  // Lfsr Type, can be FIB_XNOR or GAL_XOR
  parameter                    LfsrType  = "GAL_XOR",
  // Lfsr width
  parameter int unsigned       LfsrDw    = 32,
  // Width of input to be XOR'd into state (lfsr_q[InDw-1:0])
  parameter int unsigned       InDw      =  8,
  // Width of output tap (from lfsr_q[OutDw-1:0])
  parameter int unsigned       OutDw     =  8,
  // Lfsr reset state, must be nonzero!
  parameter logic [LfsrDw-1:0] Seed      = LfsrDw'(1),
  // Custom polynomial coeffs
  parameter logic [LfsrDw-1:0] Custom    = '0,
  // Enable this for DV, disable this for long LFSRs in FPV
  parameter bit                MaxLenSVA = 1'b1
) (
  input                    clk_i,
  input                    rst_ni,
  input                    en_i,
  input        [InDw-1:0]  data_i,
  output logic [OutDw-1:0] data_o
);

  // automatically generated with get-lfsr-coeffs.py script
  localparam int unsigned GAL_XOR_LUT_OFF = 4;
  localparam logic [63:0] GAL_XOR_COEFFS [0:60] =
    '{ 64'h9,
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

  // automatically generated with get-lfsr-coeffs.py script
  localparam int unsigned FIB_XNOR_LUT_OFF = 3;
  localparam logic [167:0] FIB_XNOR_COEFFS [0:165] =
    '{ 168'h6,
       168'hC,
       168'h14,
       168'h30,
       168'h60,
       168'hB8,
       168'h110,
       168'h240,
       168'h500,
       168'h829,
       168'h100D,
       168'h2015,
       168'h6000,
       168'hD008,
       168'h12000,
       168'h20400,
       168'h40023,
       168'h90000,
       168'h140000,
       168'h300000,
       168'h420000,
       168'hE10000,
       168'h1200000,
       168'h2000023,
       168'h4000013,
       168'h9000000,
       168'h14000000,
       168'h20000029,
       168'h48000000,
       168'h80200003,
       168'h100080000,
       168'h204000003,
       168'h500000000,
       168'h801000000,
       168'h100000001F,
       168'h2000000031,
       168'h4400000000,
       168'hA000140000,
       168'h12000000000,
       168'h300000C0000,
       168'h63000000000,
       168'hC0000030000,
       168'h1B0000000000,
       168'h300003000000,
       168'h420000000000,
       168'hC00000180000,
       168'h1008000000000,
       168'h3000000C00000,
       168'h6000C00000000,
       168'h9000000000000,
       168'h18003000000000,
       168'h30000000030000,
       168'h40000040000000,
       168'hC0000600000000,
       168'h102000000000000,
       168'h200004000000000,
       168'h600003000000000,
       168'hC00000000000000,
       168'h1800300000000000,
       168'h3000000000000030,
       168'h6000000000000000,
       168'hD800000000000000,
       168'h10000400000000000,
       168'h30180000000000000,
       168'h60300000000000000,
       168'h80400000000000000,
       168'h140000028000000000,
       168'h300060000000000000,
       168'h410000000000000000,
       168'h820000000001040000,
       168'h1000000800000000000,
       168'h3000600000000000000,
       168'h6018000000000000000,
       168'hC000000018000000000,
       168'h18000000600000000000,
       168'h30000600000000000000,
       168'h40200000000000000000,
       168'hC0000000060000000000,
       168'h110000000000000000000,
       168'h240000000480000000000,
       168'h600000000003000000000,
       168'h800400000000000000000,
       168'h1800000300000000000000,
       168'h3003000000000000000000,
       168'h4002000000000000000000,
       168'hC000000000000000018000,
       168'h10000000004000000000000,
       168'h30000C00000000000000000,
       168'h600000000000000000000C0,
       168'hC00C0000000000000000000,
       168'h140000000000000000000000,
       168'h200001000000000000000000,
       168'h400800000000000000000000,
       168'hA00000000001400000000000,
       168'h1040000000000000000000000,
       168'h2004000000000000000000000,
       168'h5000000000028000000000000,
       168'h8000000004000000000000000,
       168'h18600000000000000000000000,
       168'h30000000000000000C00000000,
       168'h40200000000000000000000000,
       168'hC0300000000000000000000000,
       168'h100010000000000000000000000,
       168'h200040000000000000000000000,
       168'h5000000000000000A0000000000,
       168'h800000010000000000000000000,
       168'h1860000000000000000000000000,
       168'h3003000000000000000000000000,
       168'h4010000000000000000000000000,
       168'hA000000000140000000000000000,
       168'h10080000000000000000000000000,
       168'h30000000000000000000180000000,
       168'h60018000000000000000000000000,
       168'hC0000000000000000300000000000,
       168'h140005000000000000000000000000,
       168'h200000001000000000000000000000,
       168'h404000000000000000000000000000,
       168'h810000000000000000000000000102,
       168'h1000040000000000000000000000000,
       168'h3000000000000006000000000000000,
       168'h5000000000000000000000000000000,
       168'h8000000004000000000000000000000,
       168'h18000000000000000000000000030000,
       168'h30000000030000000000000000000000,
       168'h60000000000000000000000000000000,
       168'hA0000014000000000000000000000000,
       168'h108000000000000000000000000000000,
       168'h240000000000000000000000000000000,
       168'h600000000000C00000000000000000000,
       168'h800000040000000000000000000000000,
       168'h1800000000000300000000000000000000,
       168'h2000000000000010000000000000000000,
       168'h4008000000000000000000000000000000,
       168'hC000000000000000000000000000000600,
       168'h10000080000000000000000000000000000,
       168'h30600000000000000000000000000000000,
       168'h4A400000000000000000000000000000000,
       168'h80000004000000000000000000000000000,
       168'h180000003000000000000000000000000000,
       168'h200001000000000000000000000000000000,
       168'h600006000000000000000000000000000000,
       168'hC00000000000000006000000000000000000,
       168'h1000000000000100000000000000000000000,
       168'h3000000000000006000000000000000000000,
       168'h6000000003000000000000000000000000000,
       168'h8000001000000000000000000000000000000,
       168'h1800000000000000000000000000C000000000,
       168'h20000000000001000000000000000000000000,
       168'h48000000000000000000000000000000000000,
       168'hC0000000000000006000000000000000000000,
       168'h180000000000000000000000000000000000000,
       168'h280000000000000000000000000000005000000,
       168'h60000000C000000000000000000000000000000,
       168'hC00000000000000000000000000018000000000,
       168'h1800000600000000000000000000000000000000,
       168'h3000000C00000000000000000000000000000000,
       168'h4000000080000000000000000000000000000000,
       168'hC000300000000000000000000000000000000000,
       168'h10000400000000000000000000000000000000000,
       168'h30000000000000000000006000000000000000000,
       168'h600000000000000C0000000000000000000000000,
       168'hC0060000000000000000000000000000000000000,
       168'h180000006000000000000000000000000000000000,
       168'h3000000000C0000000000000000000000000000000,
       168'h410000000000000000000000000000000000000000,
       168'hA00140000000000000000000000000000000000000 };

  logic lockup;
  logic [LfsrDw-1:0] lfsr_d, lfsr_q;
  logic [LfsrDw-1:0] next_lfsr_state, coeffs;

  //////////////////////////////////////////////////////
  // Galois XOR
  if (LfsrType == "GAL_XOR") begin : gen_gal_xor

    // if custom polynomial is provided
    if (Custom) begin : gen_custom
      assign coeffs = Custom[LfsrDw-1:0];
    end else begin : gen_lut
      assign coeffs = GAL_XOR_COEFFS[LfsrDw-GAL_XOR_LUT_OFF][LfsrDw-1:0];
      // check that the most significant bit of polynomial is 1
      `ASSERT_INIT(MinLfsrWidth_A, LfsrDw >= $low(GAL_XOR_COEFFS)+GAL_XOR_LUT_OFF)
      `ASSERT_INIT(MaxLfsrWidth_A, LfsrDw <= $high(GAL_XOR_COEFFS)+GAL_XOR_LUT_OFF)
    end

    // calculate next state using internal XOR feedback and entropy input
    assign next_lfsr_state = LfsrDw'(data_i) ^ ({LfsrDw{lfsr_q[0]}} & coeffs) ^ (lfsr_q >> 1);

    // lockup condition is all-zero
    assign lockup = ~(|lfsr_q);

    // check that seed is not all-zero
    `ASSERT_INIT(SeedNzCheck_A, |Seed)

  //////////////////////////////////////////////////////
  // Fibonacci XNOR
  end else if (LfsrType == "FIB_XNOR") begin : gen_fib_xnor

    // if custom polynomial is provided
    if (Custom) begin : gen_custom
      assign coeffs = Custom[LfsrDw-1:0];
    end else begin : gen_lut
      assign coeffs = FIB_XNOR_COEFFS[LfsrDw-FIB_XNOR_LUT_OFF][LfsrDw-1:0];
      // check that the most significant bit of polynomial is 1
      `ASSERT_INIT(MinLfsrWidth_A, LfsrDw >= $low(FIB_XNOR_COEFFS)+FIB_XNOR_LUT_OFF)
      `ASSERT_INIT(MaxLfsrWidth_A, LfsrDw <= $high(FIB_XNOR_COEFFS)+FIB_XNOR_LUT_OFF)
    end

    // calculate next state using external XNOR feedback and entropy input
    assign next_lfsr_state = LfsrDw'(data_i) ^ {lfsr_q[LfsrDw-2:0], ~(^(lfsr_q & coeffs))};

    // lockup condition is all-ones
    assign lockup = &lfsr_q;

    // check that seed is not all-ones
    `ASSERT_INIT(SeedNzCheck_A, !(&Seed))

  //////////////////////////////////////////////////////
  // Unknown
  end else begin : gen_unknown_type
    `ASSERT_INIT(UnknownLfsrType_A, 0)
  end

  //////////////////////////////////////////////////////
  // Shared logic
  //////////////////////////////////////////////////////

  assign lfsr_d = (en_i && lockup) ? Seed            :
                  (en_i)           ? next_lfsr_state :
                                     lfsr_q;

  assign data_o  = lfsr_q[OutDw-1:0];

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_reg
    if (!rst_ni) begin
      lfsr_q <= Seed;
    end else begin
      lfsr_q <= lfsr_d;
    end
  end


  //////////////////////////////////////////////////////
  // shared assertions
  //////////////////////////////////////////////////////

  `ASSERT_KNOWN(DataKnownO_A, data_o, clk_i, !rst_ni)

  function automatic logic[LfsrDw-1:0] compute_next_state(logic[LfsrDw-1:0] coeffs,
                                                          logic[InDw-1:0]   data,
                                                          logic[LfsrDw-1:0] state);
    logic state0;

    // Galois XOR
    if (LfsrType == "GAL_XOR") begin
      if (!state) begin
        state = Seed;
      end else begin
        state0 = state[0];
        state = state >> 1;
        if (state0) state ^= coeffs;
        state ^= LfsrDw'(data);
      end
    // Fibonacci XNOR
    end else if (LfsrType == "FIB_XNOR") begin
      if (&state) begin
        state = Seed;
      end else begin
        state0 = ~(^(state & coeffs));
        state = state << 1;
        state[0] = state0;
        state ^= LfsrDw'(data);
      end
    end else begin
      $error("unknown lfsr type");
    end

    return state;
  endfunction : compute_next_state

  `ASSERT_INIT(InputWidth_A, LfsrDw >= InDw)
  `ASSERT_INIT(OutputWidth_A, LfsrDw >= OutDw)
  // check that a stuck LFSR is correctly reseeded
  `ASSERT(LfsrLockupCheck_A, en_i && lockup |=> !lockup, clk_i, !rst_ni)
  // MSB must be one in any case
  `ASSERT(CoeffCheck_A, coeffs[LfsrDw-1], clk_i, !rst_ni)

  // check whether next state is computed correctly
  `ASSERT(NextStateCheck_A, en_i |=> lfsr_q ==
    compute_next_state(coeffs, $past(data_i,1), $past(lfsr_q,1)),
    clk_i, !rst_ni )

  // the code below is not meant to be synthesized,
  // but it is intended to be used in simulation and FPV
  // the formal tool defines SYNTHESIS, hence this workaround
`ifdef FPV_ON
  localparam bit MaxLenSVALocal = MaxLenSVA;
`else
`ifndef SYNTHESIS
  localparam bit MaxLenSVALocal = MaxLenSVA;
`else
  localparam bit MaxLenSVALocal = 1'b0;
`endif
`endif

  if (MaxLenSVALocal) begin : gen_max_len_sva
    // the code below is a workaround to enable long sequences to be checked.
    // some simulators do not support SVA sequences longer than 2**32-1.
    logic [LfsrDw-1:0] cnt_d, cnt_q;
    logic data_set_d, data_set_q;
    logic [LfsrDw-1:0] cmp_val;

    assign cmp_val = {{(LfsrDw-1){1'b1}}, 1'b0}; // 2**LfsrDw-2
    assign cnt_d = (en_i && lockup)             ? '0 :
                   (en_i && (cnt_q == cmp_val)) ? '0 :
                   (en_i)                       ? cnt_q + 1'b1 :
                                                  cnt_q;

    assign data_set_d = data_set_q | (|data_i);

    always_ff @(posedge clk_i or negedge rst_ni) begin : p_max_len
      if (!rst_ni) begin
        cnt_q      <= '0;
        data_set_q <= 1'b0;
      end else begin
        cnt_q      <= cnt_d;
        data_set_q <= data_set_d;
      end
    end

    `ASSERT(MaximalLengthCheck0_A, cnt_q == 0 |-> lfsr_q == Seed, clk_i, !rst_ni || data_set_q)
    `ASSERT(MaximalLengthCheck1_A, cnt_q != 0 |-> lfsr_q != Seed, clk_i, !rst_ni || data_set_q)
  end

endmodule
