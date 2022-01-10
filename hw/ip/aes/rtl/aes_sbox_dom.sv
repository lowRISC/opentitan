// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES S-Box with First-Order Domain-Oriented Masking
//
// This is the unpipelined version using DOM-dep multipliers. It has a latency of 5 clock cycles
// and requires 28 bits of pseudo-random data per evaluation. Pipelining would only be beneficial
// when using
// - either a cipher core architecture with a data path smaller than 128 bit, i.e., where the
//   individual S-Boxes are evaluated more than once per round, or
// - a fully unrolled cipher core architecture for maximum throughput.
//
// Note: The DOM AES S-Box is built on top of the Canright masked S-Box without mask re-use.
//
// For details, see the following papers and reports:
// [1] Gross, "Domain-Oriented Masking: Compact Masked Hardware Implementations with Arbitrary
//     Protection Order" available at https://eprint.iacr.org/2016/486.pdf
// [2] Canright, "A very compact 'perfectly masked' S-box for AES (corrected)" available at
//     https://eprint.iacr.org/2009/011.pdf
// [3] Canright, "A very compact Rijndael S-box" available at https://hdl.handle.net/10945/25608
//
// Using the Coco-Alma tool in transient mode, this implementation has been formally verified to be
// secure against first-order side-channel analysis (SCA). For more information on the tool,
// refer to the following papers:
// [4] Gigerl, "COCO: Co-design and co-verification of masked software implementations on CPUs"
//     available at https://eprint.iacr.org/2020/1294.pdf
// [5] Bloem, "Formal verification of masked hardware implementations in the presence of glitches"
//     available at https://eprint.iacr.org/2017/897.pdf

///////////////////////////////////////////////////////////////////////////////////////////////////
// IMPORTANT NOTE:                                                                               //
//                            DO NOT USE THIS FOR SYNTHESIS BLINDLY!                             //
//                                                                                               //
// This implementation relies on primitive cells like prim_buf/flop_en containing tool-specific  //
// synthesis attributes to prevent the synthesis tool from optimizing away/re-ordering registers //
// and to enforce the correct ordering of operations. Without the proper primitives, synthesis   //
// tools might heavily optimize the design. The result is likely insecure. Use with care.        //
///////////////////////////////////////////////////////////////////////////////////////////////////

`include "prim_assert.sv"

// Packed struct for pseudo-random data (PRD) input. Stages 1, 3 and 4 require 8 bits each. Stage 2
// requires just 4 bits.
typedef struct packed {
  logic [7:0] prd_1;
  logic [3:0] prd_2;
  logic [7:0] prd_3;
  logic [7:0] prd_4;
} prd_in_t;

// Packed struct for pseudo-random data (PRD) output. Stages 2 and 3 produce 8 bits each. Stage 1
// produces just 4 bits.
typedef struct packed {
  logic [3:0] prd_1;
  logic [7:0] prd_2;
  logic [7:0] prd_3;
} prd_out_t;

// DOM-indep GF(2^N) multiplier, first-order masked.
// Computes (a_q ^ b_q) = (a_x ^ b_x) * (a_y ^ b_y), i.e. q = x * y using first-order
// domain-oriented masking. The sharings of x and y are required to be uniformly random and
// independent from each other.
// See Fig. 2 in [1].
module aes_dom_indep_mul_gf2pn #(
  parameter int unsigned NPower   = 4,
  parameter bit          Pipeline = 1'b0
) (
  input  logic              clk_i,
  input  logic              rst_ni,
  input  logic              we_i,
  input  logic [NPower-1:0] a_x,    // Share a of x
  input  logic [NPower-1:0] a_y,    // Share a of y
  input  logic [NPower-1:0] b_x,    // Share b of x
  input  logic [NPower-1:0] b_y,    // Share b of y
  input  logic [NPower-1:0] z_0,    // Randomness for resharing
  output logic [NPower-1:0] a_q,    // Share a of q
  output logic [NPower-1:0] b_q     // Share b of q
);

  import aes_sbox_canright_pkg::*;

  /////////////////
  // Calculation //
  /////////////////
  // Inner-domain terms
  logic [NPower-1:0] mul_ax_ay_d, mul_bx_by_d;
  if (NPower == 4) begin : gen_inner_mul_gf2p4
    assign mul_ax_ay_d = aes_mul_gf2p4(a_x, a_y);
    assign mul_bx_by_d = aes_mul_gf2p4(b_x, b_y);

  end else begin : gen_inner_mul_gf2p2
    assign mul_ax_ay_d = aes_mul_gf2p2(a_x, a_y);
    assign mul_bx_by_d = aes_mul_gf2p2(b_x, b_y);
  end

  // Cross-domain terms
  logic [NPower-1:0] mul_ax_by, mul_ay_bx;
  if (NPower == 4) begin : gen_cross_mul_gf2p4
    assign mul_ax_by = aes_mul_gf2p4(a_x, b_y);
    assign mul_ay_bx = aes_mul_gf2p4(a_y, b_x);

  end else begin : gen_cross_mul_gf2p2
    assign mul_ax_by = aes_mul_gf2p2(a_x, b_y);
    assign mul_ay_bx = aes_mul_gf2p2(a_y, b_x);
  end

  ///////////////
  // Resharing //
  ///////////////
  // Resharing of cross-domain terms
  logic [NPower-1:0] aq_z0_d, bq_z0_d;
  logic [NPower-1:0] aq_z0_q, bq_z0_q;
  assign aq_z0_d = z_0 ^ mul_ax_by;
  assign bq_z0_d = z_0 ^ mul_ay_bx;

  // Registers
  prim_flop_en #(
    .Width      ( 2*NPower ),
    .ResetValue ( '0       )
  ) u_prim_flop_abq_z0 (
    .clk_i  ( clk_i              ),
    .rst_ni ( rst_ni             ),
    .en_i   ( we_i               ),
    .d_i    ( {aq_z0_d, bq_z0_d} ),
    .q_o    ( {aq_z0_q, bq_z0_q} )
  );

  /////////////////////////
  // Optional Pipelining //
  /////////////////////////
  logic [NPower-1:0] mul_ax_ay, mul_bx_by;

  if (Pipeline == 1'b1) begin : gen_pipeline
    // Add pipeline registers on inner-domain terms prior to integration. This allows accepting new
    // input data every clock cycle and prevents SCA leakage occurring due to the integration of
    // reshared cross-domain terms with inner-domain terms derived from different input data.

    logic [NPower-1:0] mul_ax_ay_q, mul_bx_by_q;
    prim_flop_en #(
      .Width      ( 2*NPower ),
      .ResetValue ( '0       )
    ) u_prim_flop_mul_abx_aby (
      .clk_i  ( clk_i                      ),
      .rst_ni ( rst_ni                     ),
      .en_i   ( we_i                       ),
      .d_i    ( {mul_ax_ay_d, mul_bx_by_d} ),
      .q_o    ( {mul_ax_ay_q, mul_bx_by_q} )
    );

    assign mul_ax_ay = mul_ax_ay_q;
    assign mul_bx_by = mul_bx_by_q;

  end else begin : gen_no_pipeline
    // Do not add the optional pipeline registers on the inner-domain terms. This allows to save
    // some area in case the multiplier does not need to accept new data in every cycle. However,
    // this can cause SCA leakage as during the clock cycle in which new data arrives, the new
    // inner-domain terms are integrated with the previous, reshared cross-domain terms.

    // Avoid aggressive synthesis optimizations.
    logic [NPower-1:0] mul_ax_ay_buf, mul_bx_by_buf;
    prim_buf #(
      .Width  ( 2*NPower )
    ) u_prim_buf_mul_abx_aby (
      .in_i  ( {mul_ax_ay_d,   mul_bx_by_d}   ),
      .out_o ( {mul_ax_ay_buf, mul_bx_by_buf} )
    );

    assign mul_ax_ay = mul_ax_ay_buf;
    assign mul_bx_by = mul_bx_by_buf;
  end

  /////////////////
  // Integration //
  /////////////////
  assign a_q = mul_ax_ay ^ aq_z0_q;
  assign b_q = mul_bx_by ^ bq_z0_q;

  // Only GF(2^4) and GF(2^2) is supported.
  `ASSERT_INIT(AesDomIndepMulPower, NPower == 4 || NPower == 2)

endmodule

// DOM-dep GF(2^N) multiplier, first-order masked.
// Computes (a_q ^ b_q) = (a_x ^ b_x) * (a_y ^ b_y), i.e. q = x * y using first-order
// domain-oriented masking. The sharings of x and y are NOT required to be independent from each
// other. This is the un-optimized version consuming 3 times N bits of randomness for blinding and
// resharing. It is not used in the design but we keep it for reference.
// See Fig. 4 and Formulas 8 - 11 in [1].
module aes_dom_dep_mul_gf2pn_unopt #(
  parameter int unsigned NPower   = 4,
  parameter bit          Pipeline = 1'b0
) (
  input  logic              clk_i,
  input  logic              rst_ni,
  input  logic              we_i,
  input  logic [NPower-1:0] a_x,    // Share a of x
  input  logic [NPower-1:0] a_y,    // Share a of y
  input  logic [NPower-1:0] b_x,    // Share b of x
  input  logic [NPower-1:0] b_y,    // Share b of y
  input  logic [NPower-1:0] a_z,    // Randomness for blinding
  input  logic [NPower-1:0] b_z,    // Randomness for blinding
  input  logic [NPower-1:0] z_0,    // Randomness for resharing
  output logic [NPower-1:0] a_q,    // Share a of q
  output logic [NPower-1:0] b_q     // Share b of q
);

  import aes_sbox_canright_pkg::*;

  //////////////
  // Blinding //
  //////////////
  // Blinding of y by z.
  logic [NPower-1:0] a_yz_d, b_yz_d;
  logic [NPower-1:0] a_yz_q, b_yz_q;
  assign a_yz_d = a_y ^ a_z;
  assign b_yz_d = b_y ^ b_z;

  // Registers
  prim_flop_en #(
    .Width      ( 2*NPower ),
    .ResetValue ( '0       )
  ) u_prim_flop_ab_yz (
    .clk_i  ( clk_i            ),
    .rst_ni ( rst_ni           ),
    .en_i   ( we_i             ),
    .d_i    ( {a_yz_d, b_yz_d} ),
    .q_o    ( {a_yz_q, b_yz_q} )
  );

  ////////////////
  // Correction //
  ////////////////
  logic [NPower-1:0] a_mul_x_z, b_mul_x_z;
  aes_dom_indep_mul_gf2pn #(
    .NPower   ( NPower   ),
    .Pipeline ( Pipeline )
  ) u_aes_dom_indep_mul_gf2pn (
    .clk_i  ( clk_i     ),
    .rst_ni ( rst_ni    ),
    .we_i   ( we_i      ),
    .a_x    ( a_x       ), // Share a of x
    .a_y    ( a_z       ), // Share a of z
    .b_x    ( b_x       ), // Share b of x
    .b_y    ( b_z       ), // Share b of z
    .z_0    ( z_0       ), // Randomness for resharing
    .a_q    ( a_mul_x_z ), // Share a of x * z
    .b_q    ( b_mul_x_z )  // Share b of x * z
  );

  /////////////////////////
  // Optional Pipelining //
  /////////////////////////
  logic [NPower-1:0] a_x_calc, b_x_calc;

  if (Pipeline == 1'b1) begin : gen_pipeline
    // Add pipeline registers for input x. This allows accepting new input data every clock cycle
    // and prevents SCA leakage occurring due to the multiplication of input x with b belonging to
    // different clock cycles.

    logic [NPower-1:0] a_x_q, b_x_q;
    prim_flop_en #(
      .Width      ( 2*NPower ),
      .ResetValue ( '0       )
    ) u_prim_flop_ab_x (
      .clk_i  ( clk_i          ),
      .rst_ni ( rst_ni         ),
      .en_i   ( we_i           ),
      .d_i    ( {a_x,   b_x}   ),
      .q_o    ( {a_x_q, b_x_q} )
    );

    assign a_x_calc = a_x_q;
    assign b_x_calc = b_x_q;

  end else begin : gen_no_pipeline
    // Do not add the optional pipeline registers for input x. This allows to save some area in
    // case the multiplier does not need to accept new data in every cycle. However, this can cause
    // SCA leakage as during the clock cycle in which new data arrives, the new x input is
    // multiplied with the previous b.

    assign a_x_calc = a_x;
    assign b_x_calc = b_x;
  end

  /////////////////
  // Calculation //
  /////////////////
  // Combine shares of blinded y to obtain b.
  logic [NPower-1:0] b;
  assign b = a_yz_q ^ b_yz_q;

  logic [NPower-1:0] a_mul_ax_b, b_mul_bx_b;
  if (NPower == 4) begin : gen_mul_gf2p4
    assign a_mul_ax_b = aes_mul_gf2p4(a_x_calc, b);
    assign b_mul_bx_b = aes_mul_gf2p4(b_x_calc, b);

  end else begin : gen_mul_gf2p2
    assign a_mul_ax_b = aes_mul_gf2p2(a_x_calc, b);
    assign b_mul_bx_b = aes_mul_gf2p2(b_x_calc, b);
  end

  /////////////////
  // Integration //
  /////////////////
  assign a_q = a_mul_x_z ^ a_mul_ax_b;
  assign b_q = b_mul_x_z ^ b_mul_bx_b;

  // Only GF(2^4) and GF(2^2) is supported.
  `ASSERT_INIT(AesDomDepMulUnoptPower, NPower == 4 || NPower == 2)

endmodule

// DOM-dep GF(2^N) multiplier, first-order masked.
// Computes (a_q ^ b_q) = (a_x ^ b_x) * (a_y ^ b_y), i.e. q = x * y using first-order
// domain-oriented masking. The sharings of x and y are NOT required to be independent from each
// other. This is the optimized version consuming 2 instead of 3 times N bits of randomness for
// blinding and resharing.
// See Formula 12 in [1].
module aes_dom_dep_mul_gf2pn #(
  parameter int unsigned NPower      = 4,
  parameter bit          Pipeline    = 1'b0,
  parameter bit          PreDomIndep = 1'b0 // 1'b0: Not followed by an un-pipelined DOM-indep
                                            //       multiplier, this enables additional area
                                            //       optimizations
                                            // 1'b1: Directly followed by an un-pipelined
                                            //       DOM-indep multiplier, this is the version
                                            //       discussed in [1].
) (
  input  logic                clk_i,
  input  logic                rst_ni,
  input  logic                we_i,
  input  logic   [NPower-1:0] a_x,    // Share a of x
  input  logic   [NPower-1:0] a_y,    // Share a of y
  input  logic   [NPower-1:0] b_x,    // Share b of x
  input  logic   [NPower-1:0] b_y,    // Share b of y
  input  logic   [NPower-1:0] a_x_q,  // Share a of x, pipelined (for Pipeline=1 or PreDomIndep=1)
  input  logic   [NPower-1:0] a_y_q,  // Share a of y, pipelined (for Pipeline=1)
  input  logic   [NPower-1:0] b_x_q,  // Share b of x, pipelined (for Pipeline=1 or PreDomIndep=1)
  input  logic   [NPower-1:0] b_y_q,  // Share b of y, pipelined (for Pipeline=1)
  input  logic   [NPower-1:0] z_0,    // Randomness for blinding
  input  logic   [NPower-1:0] z_1,    // Randomness for resharing
  output logic   [NPower-1:0] a_q,    // Share a of q
  output logic   [NPower-1:0] b_q,    // Share b of q
  output logic [2*NPower-1:0] prd_o   // Randomness for use in another S-Box instance
);

  import aes_sbox_canright_pkg::*;

  //////////////
  // Blinding //
  //////////////
  // Blinding of y by z_0.
  logic [NPower-1:0] a_yz0_d, b_yz0_d;
  logic [NPower-1:0] a_yz0_q, b_yz0_q;
  assign a_yz0_d = a_y ^ z_0;
  assign b_yz0_d = b_y ^ z_0;

  // Registers
  prim_flop_en #(
    .Width      ( 2*NPower ),
    .ResetValue ( '0       )
  ) u_prim_flop_ab_yz0 (
    .clk_i  ( clk_i              ),
    .rst_ni ( rst_ni             ),
    .en_i   ( we_i               ),
    .d_i    ( {a_yz0_d, b_yz0_d} ),
    .q_o    ( {a_yz0_q, b_yz0_q} )
  );

  ////////////////
  // Correction //
  ////////////////
  // Basically, this a DOM-indep multiplier with:
  // - a_x = a_x, b_x = b_x, and
  // - a_y = z_0, b_y = 0 (constant),
  // which allows for further optimizations.

  // Calculation
  logic [NPower-1:0] mul_ax_z0, mul_bx_z0;
  if (NPower == 4) begin : gen_corr_mul_gf2p4
    assign mul_ax_z0 = aes_mul_gf2p4(a_x, z_0);
    assign mul_bx_z0 = aes_mul_gf2p4(b_x, z_0);

  end else begin : gen_corr_mul_gf2p2
    assign mul_ax_z0 = aes_mul_gf2p2(a_x, z_0);
    assign mul_bx_z0 = aes_mul_gf2p2(b_x, z_0);
  end

  // Avoid aggressive synthesis optimizations.
  logic [NPower-1:0] mul_ax_z0_buf, mul_bx_z0_buf;
  prim_buf #(
    .Width ( 2*NPower )
  ) u_prim_buf_mul_abx_z0 (
    .in_i  ( {mul_ax_z0,     mul_bx_z0}     ),
    .out_o ( {mul_ax_z0_buf, mul_bx_z0_buf} )
  );

  // Resharing
  logic [NPower-1:0] axz0_z1_d, bxz0_z1_d;
  logic [NPower-1:0] axz0_z1_q, bxz0_z1_q;
  assign axz0_z1_d = mul_ax_z0_buf ^ z_1;
  assign bxz0_z1_d = mul_bx_z0_buf ^ z_1;

  // Registers
  prim_flop_en #(
    .Width      ( 2*NPower ),
    .ResetValue ( '0       )
  ) u_prim_flop_abxz0_z1 (
    .clk_i  ( clk_i                  ),
    .rst_ni ( rst_ni                 ),
    .en_i   ( we_i                   ),
    .d_i    ( {axz0_z1_d, bxz0_z1_d} ),
    .q_o    ( {axz0_z1_q, bxz0_z1_q} )
  );

  // Use intermediate results for generating PRD for another S-Box instance.
  // Use one share only. Directly use output of flops updating with we_i.
  // These intermediate results are obtained by remasking b_y and mul_bx_z0 with z_0 and z_1,
  // respectively. Since z_0/1 are uniformly distributed and independent of b_y and mul_bx_z0,
  // the intermediate results are also uniformly distributed and independent of b_y and mul_bx_z0.
  // For details, see Lemma 1 in [2].
  assign prd_o = {b_yz0_q, bxz0_z1_q};

  /////////////////////////
  // Optional Pipelining //
  /////////////////////////
  logic [NPower-1:0] a_x_calc, b_x_calc, a_y_calc, b_y_calc;

  if (Pipeline == 1'b1 && PreDomIndep != 1'b1) begin : gen_pipeline_use
    // Use pipelined inputs x and y. This allows accepting new input data every clock cycle and
    // prevents SCA leakage occurring due to the multiplication of inputs x and y with d_b
    // belonging to different clock cycles.
    //
    // The PreDomIndep variant uses the pipelined inputs directly.

    assign a_x_calc = a_x_q;
    assign b_x_calc = b_x_q;
    assign a_y_calc = a_y_q;
    assign b_y_calc = b_y_q;

  end else begin : gen_no_pipeline_use
    // Do not use pipelined inputs x and y. This allows to save some area in case the multiplier
    // does not need to accept new data in every cycle. However, this can cause SCA leakage as
    // during the clock cycle in which new data arrives, the new x and y inputs are multiplied
    // with the previous d_b.

    assign a_x_calc = a_x;
    assign b_x_calc = b_x;
    assign a_y_calc = a_y;
    assign b_y_calc = b_y;

    // Tie off unused signals.
    if (PreDomIndep != 1'b1) begin : gen_ab_x_q
      logic [NPower-1:0] unused_a_x_q, unused_b_x_q;
      assign unused_a_x_q = a_x_q;
      assign unused_b_x_q = b_x_q;
    end
    logic [NPower-1:0] unused_a_y_q, unused_b_y_q;
    assign unused_a_y_q = a_y_q;
    assign unused_b_y_q = b_y_q;
  end

  ///////////////////////////////
  // Calculation & Integration //
  ///////////////////////////////
  // Compute b. Note that unlike for the unoptimized implementation, we don't combine the blinded
  // shares of y to obtain a single b value. Intstead, every domain d gets its own version of b:
  //
  //   d_b = d_y ^ _D_y_z0
  //
  // where _D_y_z0 corresponds to the sum of all domains of y except for domain d, each
  // individually blinded by z0 (needs to happen before the register bank). This optimization
  // is only suitable for first-order masking.
  // See Formula 12 in [1].

  if (PreDomIndep == 1'b1) begin : gen_pre_dom_indep
    // This DOM-dep multiplier is directly followed by an un-pipelined DOM-indep multiplier. To
    // prevent SCA leakage in the un-pipelined DOM-indep multiplier, the d_y and _D_y_z0 parts of
    // d_b need to be individually multiplied with input x and then the results need to be
    // integrated (summed up) on a per-domain basis.

    // d_y part: Inner-domain terms of x * y
    logic [NPower-1:0] mul_ax_ay_d, mul_bx_by_d;
    logic [NPower-1:0] mul_ax_ay_q, mul_bx_by_q;
    if (NPower == 4) begin : gen_inner_mul_gf2p4
      assign mul_ax_ay_d = aes_mul_gf2p4(a_x_calc, a_y_calc);
      assign mul_bx_by_d = aes_mul_gf2p4(b_x_calc, b_y_calc);

    end else begin : gen_inner_mul_gf2p2
      assign mul_ax_ay_d = aes_mul_gf2p2(a_x_calc, a_y_calc);
      assign mul_bx_by_d = aes_mul_gf2p2(b_x_calc, b_y_calc);
    end

    // Registers
    prim_flop_en #(
      .Width      ( 2*NPower ),
      .ResetValue ( '0       )
    ) u_prim_flop_mul_abx_aby (
      .clk_i  ( clk_i                      ),
      .rst_ni ( rst_ni                     ),
      .en_i   ( we_i                       ),
      .d_i    ( {mul_ax_ay_d, mul_bx_by_d} ),
      .q_o    ( {mul_ax_ay_q, mul_bx_by_q} )
    );

    // _D_y_z0 part: Cross-domain terms: d_x * _D_y_z0
    // Need to use registered version of input x.
    logic [NPower-1:0] mul_ax_byz0, mul_bx_ayz0;
    if (NPower == 4) begin : gen_cross_mul_gf2p4
      assign mul_ax_byz0 = aes_mul_gf2p4(a_x_q, b_yz0_q);
      assign mul_bx_ayz0 = aes_mul_gf2p4(b_x_q, a_yz0_q);

    end else begin : gen_cross_mul_gf2p2
      assign mul_ax_byz0 = aes_mul_gf2p2(a_x_q, b_yz0_q);
      assign mul_bx_ayz0 = aes_mul_gf2p2(b_x_q, a_yz0_q);
    end

    // Avoid aggressive synthesis optimizations.
    logic [NPower-1:0] mul_ax_byz0_buf, mul_bx_ayz0_buf;
    prim_buf #(
      .Width ( 2*NPower )
    ) u_prim_buf_mul_abx_bayz0 (
      .in_i  ( {mul_ax_byz0,     mul_bx_ayz0}     ),
      .out_o ( {mul_ax_byz0_buf, mul_bx_ayz0_buf} )
    );

    // Integration
    assign a_q = axz0_z1_q ^ mul_ax_ay_q ^ mul_ax_byz0_buf;
    assign b_q = bxz0_z1_q ^ mul_bx_by_q ^ mul_bx_ayz0_buf;

  end else begin : gen_not_pre_dom_indep
    // This DOM-dep multiplier is not directly followed by an un-pipelined DOM-indep multiplier. As
    // a result, the the d_y and _D_y_z0 parts of d_b can be summed up prior to the multiplication
    // with input x which allows saving 2 GF multipliers.

    // Sum up d_y and _D_y_z0.
    logic [NPower-1:0] a_b, b_b;
    assign a_b = a_y_calc ^ b_yz0_q;
    assign b_b = b_y_calc ^ a_yz0_q;

    // Avoid aggressive synthesis optimizations.
    logic [NPower-1:0] a_b_buf, b_b_buf;
    prim_buf #(
      .Width ( 2*NPower )
    ) u_prim_buf_ab_b (
      .in_i  ( {a_b,     b_b}     ),
      .out_o ( {a_b_buf, b_b_buf} )
    );

    // GF multiplications
    logic [NPower-1:0] a_mul_ax_b, b_mul_bx_b;
    if (NPower == 4) begin : gen_mul_gf2p4
      assign a_mul_ax_b = aes_mul_gf2p4(a_x_calc, a_b_buf);
      assign b_mul_bx_b = aes_mul_gf2p4(b_x_calc, b_b_buf);
    end else begin : gen_mul_gf2p2
      assign a_mul_ax_b = aes_mul_gf2p2(a_x_calc, a_b_buf);
      assign b_mul_bx_b = aes_mul_gf2p2(b_x_calc, b_b_buf);
    end

    // Avoid aggressive synthesis optimizations.
    logic [NPower-1:0] a_mul_ax_b_buf, b_mul_bx_b_buf;
    prim_buf #(
      .Width ( 2*NPower )
    ) u_prim_buf_ab_mul_abx_b (
      .in_i  ( {a_mul_ax_b,     b_mul_bx_b}     ),
      .out_o ( {a_mul_ax_b_buf, b_mul_bx_b_buf} )
    );

    // Integration
    assign a_q = axz0_z1_q ^ a_mul_ax_b_buf;
    assign b_q = bxz0_z1_q ^ b_mul_bx_b_buf;
  end

  // Only GF(2^4) and GF(2^2) is supported.
  `ASSERT_INIT(AesDomDepMulPower, NPower == 4 || NPower == 2)

endmodule

// Inverse in GF(2^4) using first-order domain-oriented masking and normal basis [z^4, z].
// See Fig. 6 in [2] (grey block, Stages 2 and 3) and Formulas 6, 13, 14, 15, 16, 17 in [2].
module aes_dom_inverse_gf2p4 #(
  parameter bit PipelineMul = 1'b1
) (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic  [1:0] we_i,
  input  logic  [3:0] a_gamma,
  input  logic  [3:0] b_gamma,
  input  logic  [3:0] prd_2_i,
  input  logic  [7:0] prd_3_i,
  output logic  [3:0] a_gamma_inv,
  output logic  [3:0] b_gamma_inv,
  output logic  [7:0] prd_2_o,
  output logic  [7:0] prd_3_o
);

  import aes_sbox_canright_pkg::*;

  /////////////
  // Stage 2 //
  /////////////
  // Formula 13 in [2].

  logic [1:0] a_gamma1, a_gamma0, b_gamma1, b_gamma0, a_gamma1_gamma0, b_gamma1_gamma0;
  assign a_gamma1 = a_gamma[3:2];
  assign a_gamma0 = a_gamma[1:0];
  assign b_gamma1 = b_gamma[3:2];
  assign b_gamma0 = b_gamma[1:0];

  logic [1:0] a_gamma_ss_d, b_gamma_ss_d;
  logic [1:0] a_gamma_ss_q, b_gamma_ss_q;
  assign a_gamma_ss_d = aes_scale_omega2_gf2p2(aes_square_gf2p2(a_gamma1 ^ a_gamma0));
  assign b_gamma_ss_d = aes_scale_omega2_gf2p2(aes_square_gf2p2(b_gamma1 ^ b_gamma0));
  prim_flop_en #(
    .Width      ( 4  ),
    .ResetValue ( '0 )
  ) u_prim_flop_ab_gamma_ss (
    .clk_i  ( clk_i                        ),
    .rst_ni ( rst_ni                       ),
    .en_i   ( we_i[0]                      ),
    .d_i    ( {a_gamma_ss_d, b_gamma_ss_d} ),
    .q_o    ( {a_gamma_ss_q, b_gamma_ss_q} )
  );

  logic [1:0] a_gamma1_q, a_gamma0_q, b_gamma1_q, b_gamma0_q;
  prim_flop_en #(
    .Width      ( 8  ),
    .ResetValue ( '0 )
  ) u_prim_flop_ab_gamma10 (
    .clk_i  ( clk_i                                            ),
    .rst_ni ( rst_ni                                           ),
    .en_i   ( we_i[0]                                          ),
    .d_i    ( {a_gamma1,   a_gamma0,   b_gamma1,   b_gamma0}   ),
    .q_o    ( {a_gamma1_q, a_gamma0_q, b_gamma1_q, b_gamma0_q} )
  );

  logic [3:0] b_gamma10_prd2;
  aes_dom_dep_mul_gf2pn #(
    .NPower      ( 2           ),
    .Pipeline    ( PipelineMul ),
    .PreDomIndep ( 1'b0        )
  ) u_aes_dom_mul_gamma1_gamma0 (
    .clk_i  ( clk_i           ),
    .rst_ni ( rst_ni          ),
    .we_i   ( we_i[0]         ),
    .a_x    ( a_gamma1        ), // Share a of x
    .a_y    ( a_gamma0        ), // Share a of y
    .b_x    ( b_gamma1        ), // Share b of x
    .b_y    ( b_gamma0        ), // Share b of y
    .a_x_q  ( a_gamma1_q      ), // Share a of x, pipelined (for Pipeline=1 or PreDomIndep=1)
    .a_y_q  ( a_gamma0_q      ), // Share a of y, pipelined (for Pipeline=1)
    .b_x_q  ( b_gamma1_q      ), // Share b of x, pipelined (for Pipeline=1 or PreDomIndep=1)
    .b_y_q  ( b_gamma0_q      ), // Share b of y, pipelined (for Pipeline=1)
    .z_0    ( prd_2_i[1:0]    ), // Randomness for blinding
    .z_1    ( prd_2_i[3:2]    ), // Randomness for resharing
    .a_q    ( a_gamma1_gamma0 ), // Share a of q
    .b_q    ( b_gamma1_gamma0 ), // Share b of q
    .prd_o  ( b_gamma10_prd2  )  // Randomness for use in another S-Box instance
  );

  // Use intermediate results for generating PRD for Stage 3 of another S-Box instance.
  // Use one share only. Directly use output of flops updating with we_i[0].
  // b_gamma10_prd2 is based on b_gamma1_q, b_gamma0_q but XORed with prd_2_i, thus uniformly
  // distributed and independent of b_gamma1/0_q (See Lemma 1 in [2]).
  //
  // In Stage 3 of another S-Box instance, the MSBs and LSBs of the term below are used:
  // 1. as randomness in the DOM-dep multipliers u_aes_dom_mul_omega_gamma1/0, and
  // 2. to generate randomness for the DOM-indep multipliers u_aes_dom_mul_theta_y1/0 in Stage 4 of
  //    yet another S-Box instance, respectively.
  // Without interleaving b_gamma1/0_q as well as the upper and lower halves of b_gamma10_prd2 here,
  // a glitch on the write-enable signal on the input pipeline register of these DOM-indep
  // multipliers may result in undesirable SCA leakage.
  assign prd_2_o = {b_gamma1_q, b_gamma10_prd2[3:2], b_gamma0_q, b_gamma10_prd2[1:0]};

  /////////////
  // Stage 3 //
  /////////////

  // Formulas 14 and 15 in [2].
  logic [1:0] a_omega, b_omega;
  assign a_omega = aes_square_gf2p2(a_gamma1_gamma0 ^ a_gamma_ss_q);
  assign b_omega = aes_square_gf2p2(b_gamma1_gamma0 ^ b_gamma_ss_q);

  // Avoid aggressive synthesis optimizations.
  logic [1:0] a_omega_buf, b_omega_buf;
  prim_buf #(
    .Width ( 4 )
  ) u_prim_buf_ab_omega (
    .in_i  ( {a_omega,     b_omega}     ),
    .out_o ( {a_omega_buf, b_omega_buf} )
  );

  // Pipeline registers
  logic [1:0] a_gamma1_qq, a_gamma0_qq, b_gamma1_qq, b_gamma0_qq, a_omega_buf_q, b_omega_buf_q;
  if (PipelineMul == 1'b1) begin: gen_prim_flop_omega_gamma10
    // We instantiate the input pipeline registers for the DOM-dep multiplier outside of the
    // multiplier to enable sharing of pipeline registers where applicable.

    prim_flop_en #(
      .Width      ( 8  ),
      .ResetValue ( '0 )
    ) u_prim_flop_ab_gamma10_q (
      .clk_i  ( clk_i                                                ),
      .rst_ni ( rst_ni                                               ),
      .en_i   ( we_i[1]                                              ),
      .d_i    ( {a_gamma1_q,  a_gamma0_q,  b_gamma1_q,  b_gamma0_q}  ),
      .q_o    ( {a_gamma1_qq, a_gamma0_qq, b_gamma1_qq, b_gamma0_qq} )
    );

    // These inputs are used by both DOM-dep multipliers below.
    prim_flop_en #(
      .Width      ( 4  ),
      .ResetValue ( '0 )
    ) u_prim_flop_ab_omega_buf (
      .clk_i  ( clk_i                          ),
      .rst_ni ( rst_ni                         ),
      .en_i   ( we_i[1]                        ),
      .d_i    ( {a_omega_buf,   b_omega_buf}   ),
      .q_o    ( {a_omega_buf_q, b_omega_buf_q} )
    );

  end else begin : gen_no_prim_flop_ab_y10
    // When using un-pipelined multipliers, there is no need to insert additional registers.
    // We drive the corresponding inputs to 0 to make sure the functionality isn't correct in case
    // the pipeliend inputs are erroneously used.

    assign a_gamma1_qq = '0;
    assign a_gamma0_qq = '0;
    assign b_gamma1_qq = '0;
    assign b_gamma0_qq = '0;
    assign a_omega_buf_q = '0;
    assign b_omega_buf_q = '0;
  end

  // Formulas 16 and 17 in [2].
  logic [3:0] b_gamma1_omega_prd3;
  aes_dom_dep_mul_gf2pn #(
    .NPower      ( 2           ),
    .Pipeline    ( PipelineMul ),
    .PreDomIndep ( 1'b0        )
  ) u_aes_dom_mul_omega_gamma1 (
    .clk_i  ( clk_i               ),
    .rst_ni ( rst_ni              ),
    .we_i   ( we_i[1]             ),
    .a_x    ( a_gamma1_q          ), // Share a of x
    .a_y    ( a_omega_buf         ), // Share a of y
    .b_x    ( b_gamma1_q          ), // Share b of x
    .b_y    ( b_omega_buf         ), // Share b of y
    .a_x_q  ( a_gamma1_qq         ), // Share a of x, pipelined (for Pipeline=1 or PreDomIndep=1)
    .a_y_q  ( a_omega_buf_q       ), // Share a of y, pipelined (for Pipeline=1)
    .b_x_q  ( b_gamma1_qq         ), // Share b of x, pipelined (for Pipeline=1 or PreDomIndep=1)
    .b_y_q  ( b_omega_buf_q       ), // Share b of y, pipelined (for Pipeline=1)
    .z_0    ( prd_3_i[5:4]        ), // Randomness for blinding
    .z_1    ( prd_3_i[7:6]        ), // Randomness for resharing
    .a_q    ( a_gamma_inv[1:0]    ), // Share a of q
    .b_q    ( b_gamma_inv[1:0]    ), // Share b of q
    .prd_o  ( b_gamma1_omega_prd3 )  // Randomness for use in another S-Box instance
  );

  logic [3:0] b_gamma0_omega_prd3;
  aes_dom_dep_mul_gf2pn #(
    .NPower      ( 2           ),
    .Pipeline    ( PipelineMul ),
    .PreDomIndep ( 1'b0        )
  ) u_aes_dom_mul_omega_gamma0 (
    .clk_i  ( clk_i               ),
    .rst_ni ( rst_ni              ),
    .we_i   ( we_i[1]             ),
    .a_x    ( a_omega_buf         ), // Share a of x
    .a_y    ( a_gamma0_q          ), // Share a of y
    .b_x    ( b_omega_buf         ), // Share b of x
    .b_y    ( b_gamma0_q          ), // Share b of y
    .a_x_q  ( a_omega_buf_q       ), // Share a of x, pipelined (for Pipeline=1 or PreDomIndep=1)
    .a_y_q  ( a_gamma0_qq         ), // Share a of y, pipelined (for Pipeline=1)
    .b_x_q  ( b_omega_buf_q       ), // Share b of x, pipelined (for Pipeline=1 or PreDomIndep=1)
    .b_y_q  ( b_gamma0_qq         ), // Share b of y, pipelined (for Pipeline=1)
    .z_0    ( prd_3_i[1:0]        ), // Randomness for blinding
    .z_1    ( prd_3_i[3:2]        ), // Randomness for resharing
    .a_q    ( a_gamma_inv[3:2]    ), // Share a of q
    .b_q    ( b_gamma_inv[3:2]    ), // Share b of q
    .prd_o  ( b_gamma0_omega_prd3 )  // Randomness for use in another S-Box instance
  );

  // Use intermediate results for generating PRD for Stage 4 of another S-Box instance.
  // Use one share only. Directly use output of flops updating with we_i[1].
  // b_gamma1/0_omega_prd3 are both based on b_omega but XORed with differend parts of prd_3_i,
  // thus uniformly distributed and independent of b_omega (see Lemma 1 in [2]).
  assign prd_3_o = {b_gamma1_omega_prd3, b_gamma0_omega_prd3};

endmodule

// Inverse in GF(2^8) using first-order domain-oriented masking and normal basis [y^16, y].
// See Fig. 6 in [1] and Formulas 3, 12, 18 and 19 in [2].
module aes_dom_inverse_gf2p8 #(
  parameter bit PipelineMul = 1'b1
) (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic  [3:0] we_i,
  input  logic  [7:0] a_y,     // input data masked by b_y
  input  logic  [7:0] b_y,     // input mask
  input  prd_in_t     prd_i,   // pseudo-random data, e.g. for intermediate masks
  output logic  [7:0] a_y_inv, // output data masked by b_y_inv
  output logic  [7:0] b_y_inv, // output mask
  output prd_out_t    prd_o    // pseudo-random data, e.g. for use in another S-Box instance
);

  import aes_sbox_canright_pkg::*;

  /////////////
  // Stage 1 //
  /////////////
  // Formula 12 in [2].

  logic [3:0] a_y1, a_y0, b_y1, b_y0, a_y1_y0, b_y1_y0;
  assign a_y1 = a_y[7:4];
  assign a_y0 = a_y[3:0];
  assign b_y1 = b_y[7:4];
  assign b_y0 = b_y[3:0];

  logic [3:0] a_y_ss_d, b_y_ss_d;
  logic [3:0] a_y_ss_q, b_y_ss_q;
  assign a_y_ss_d = aes_square_scale_gf2p4_gf2p2(a_y1 ^ a_y0);
  assign b_y_ss_d = aes_square_scale_gf2p4_gf2p2(b_y1 ^ b_y0);
  prim_flop_en #(
    .Width      ( 8  ),
    .ResetValue ( '0 )
  ) u_prim_flop_ab_y_ss (
    .clk_i  ( clk_i                ),
    .rst_ni ( rst_ni               ),
    .en_i   ( we_i[0]              ),
    .d_i    ( {a_y_ss_d, b_y_ss_d} ),
    .q_o    ( {a_y_ss_q, b_y_ss_q} )
  );

  logic [3:0] a_y1_q, a_y0_q, b_y1_q, b_y0_q;
  if (PipelineMul == 1'b1) begin: gen_prim_flop_ab_y10
    // We instantiate the input pipeline registers for the DOM-dep multiplier outside of the
    // multiplier to enable sharing of pipeline registers where applicable.

    prim_flop_en #(
      .Width      ( 16  ),
      .ResetValue ( '0  )
    ) u_prim_flop_ab_y10 (
      .clk_i  ( clk_i                            ),
      .rst_ni ( rst_ni                           ),
      .en_i   ( we_i[0]                          ),
      .d_i    ( {a_y1,   a_y0,   b_y1,   b_y0}   ),
      .q_o    ( {a_y1_q, a_y0_q, b_y1_q, b_y0_q} )
    );

  end else begin : gen_no_prim_flop_ab_y10
    // When using un-pipelined multipliers, there is no need to insert additional registers.
    // We drive the corresponding inputs to 0 to make sure the functionality isn't correct in case
    // the pipeliend inputs are erroneously used.

    assign a_y1_q = '0;
    assign a_y0_q = '0;
    assign b_y1_q = '0;
    assign b_y0_q = '0;
  end

  logic [7:0] b_y10_prd1;
  aes_dom_dep_mul_gf2pn #(
    .NPower      ( 4           ),
    .Pipeline    ( PipelineMul ),
    .PreDomIndep ( 1'b0        )
  ) u_aes_dom_mul_y1_y0 (
    .clk_i  ( clk_i            ),
    .rst_ni ( rst_ni           ),
    .we_i   ( we_i[0]          ),
    .a_x    ( a_y1             ), // Share a of x
    .a_y    ( a_y0             ), // Share a of y
    .b_x    ( b_y1             ), // Share b of x
    .b_y    ( b_y0             ), // Share b of y
    .a_x_q  ( a_y1_q           ), // Share a of x, pipelined (for Pipeline=1 or PreDomIndep=1)
    .a_y_q  ( a_y0_q           ), // Share a of y, pipelined (for Pipeline=1)
    .b_x_q  ( b_y1_q           ), // Share b of x, pipelined (for Pipeline=1 or PreDomIndep=1)
    .b_y_q  ( b_y0_q           ), // Share b of y, pipelined (for Pipeline=1)
    .z_0    ( prd_i.prd_1[3:0] ), // Randomness for blinding
    .z_1    ( prd_i.prd_1[7:4] ), // Randomness for resharing
    .a_q    ( a_y1_y0          ), // Share a of q
    .b_q    ( b_y1_y0          ), // Share b of q
    .prd_o  ( b_y10_prd1       )  // Randomness for use in another S-Box instance
  );

  logic [3:0] a_gamma, b_gamma;
  assign a_gamma = a_y_ss_q ^ a_y1_y0;
  assign b_gamma = b_y_ss_q ^ b_y1_y0;

  // Avoid aggressive synthesis optimizations.
  logic [3:0] a_gamma_buf, b_gamma_buf;
  prim_buf #(
    .Width ( 8 )
  ) u_prim_buf_ab_gamma (
    .in_i  ( {a_gamma,     b_gamma}     ),
    .out_o ( {a_gamma_buf, b_gamma_buf} )
  );

  // Use intermediate results for generating PRD for Stage 2 of another S-Box instance.
  // Use one share only. Directly use output of flops updating with we_i[0].
  // b_y10_prd1 is based on b_y and XORed with prd_1. We just use the lower part involving a
  // non-linear element.
  assign prd_o.prd_1 = b_y10_prd1[3:0];
  logic [3:0] unused_prd;
  assign unused_prd  = b_y10_prd1[7:4];

  ////////////////////
  // Stages 2 and 3 //
  ////////////////////

  logic [3:0] a_theta, b_theta;

  // a_gamma is masked by b_gamma, a_gamma_inv is masked by b_gamma_inv.
  aes_dom_inverse_gf2p4 #(
    .PipelineMul ( PipelineMul )
  ) u_aes_dom_inverse_gf2p4 (
    .clk_i       ( clk_i       ),
    .rst_ni      ( rst_ni      ),
    .we_i        ( we_i[2:1]   ),
    .a_gamma     ( a_gamma_buf ),
    .b_gamma     ( b_gamma_buf ),
    .prd_2_i     ( prd_i.prd_2 ),
    .prd_3_i     ( prd_i.prd_3 ),
    .a_gamma_inv ( a_theta     ),
    .b_gamma_inv ( b_theta     ),
    .prd_2_o     ( prd_o.prd_2 ),
    .prd_3_o     ( prd_o.prd_3 )
  );

  /////////////
  // Stage 4 //
  /////////////
  // Formulas 18 and 19 in [2].

  logic [3:0] a_y1_qqq, a_y0_qqq, b_y1_qqq, b_y0_qqq;
  prim_flop_en #(
    .Width      ( 16 ),
    .ResetValue ( '0 )
  ) u_prim_flop_ab_y10_qqq (
    .clk_i  ( clk_i                                    ),
    .rst_ni ( rst_ni                                   ),
    .en_i   ( we_i[2]                                  ),
    .d_i    ( {a_y1,     a_y0,     b_y1,     b_y0}     ),
    .q_o    ( {a_y1_qqq, a_y0_qqq, b_y1_qqq, b_y0_qqq} )
  );

  aes_dom_indep_mul_gf2pn #(
    .NPower   ( 4           ),
    .Pipeline ( PipelineMul )
  ) u_aes_dom_mul_theta_y1 (
    .clk_i  ( clk_i            ),
    .rst_ni ( rst_ni           ),
    .we_i   ( we_i[3]          ),
    .a_x    ( a_y1_qqq         ), // Share a of x
    .a_y    ( a_theta          ), // Share a of y
    .b_x    ( b_y1_qqq         ), // Share b of x
    .b_y    ( b_theta          ), // Share b of y
    .z_0    ( prd_i.prd_4[7:4] ), // Randomness for resharing
    .a_q    ( a_y_inv[3:0]     ), // Share a of q
    .b_q    ( b_y_inv[3:0]     )  // Share b of q
  );

  aes_dom_indep_mul_gf2pn #(
    .NPower   ( 4           ),
    .Pipeline ( PipelineMul )
  ) u_aes_dom_mul_theta_y0 (
    .clk_i  ( clk_i            ),
    .rst_ni ( rst_ni           ),
    .we_i   ( we_i[3]          ),
    .a_x    ( a_theta          ), // Share a of x
    .a_y    ( a_y0_qqq         ), // Share a of y
    .b_x    ( b_theta          ), // Share b of x
    .b_y    ( b_y0_qqq         ), // Share b of y
    .z_0    ( prd_i.prd_4[3:0] ), // Randomness for resharing
    .a_q    ( a_y_inv[7:4]     ), // Share a of q
    .b_q    ( b_y_inv[7:4]     )  // Share b of q
  );

endmodule

// SEC_CM: KEY.MASKING
module aes_sbox_dom
#(
  parameter bit PipelineMul = 1'b1
) (
  input  logic              clk_i,
  input  logic              rst_ni,
  input  logic              en_i,
  output logic              out_req_o,
  input  logic              out_ack_i,
  input  aes_pkg::ciph_op_e op_i,
  input  logic        [7:0] data_i, // masked, the actual input data is data_i ^ mask_i
  input  logic        [7:0] mask_i, // input mask
  input  logic       [27:0] prd_i,  // pseudo-random data for remasking, in total we need 28 bits
                                    // of PRD per evaluation, but at most 8 bits per cycle
  output logic        [7:0] data_o, // masked, the actual output data is data_o ^ mask_o
  output logic        [7:0] mask_o, // output mask
  output logic       [19:0] prd_o   // PRD for usage in Stages 2 - 4 of other S-Box instances
);

  import aes_pkg::*;
  import aes_sbox_canright_pkg::*;

  logic [7:0] in_data_basis_x, out_data_basis_x;
  logic [7:0] in_mask_basis_x, out_mask_basis_x;
  logic [3:0] we;
  logic [7:0] prd1_d, prd1_q;
  prd_in_t    in_prd;
  prd_out_t   out_prd;

  // Convert data to normal basis X.
  assign in_data_basis_x = (op_i == CIPH_FWD) ? aes_mvm(data_i, A2X)         :
                           (op_i == CIPH_INV) ? aes_mvm(data_i ^ 8'h63, S2X) :
                                                aes_mvm(data_i, A2X);

  // Convert mask to normal basis X.
  // The addition of constant 8'h63 prior to the affine transformation is skipped.
  assign in_mask_basis_x = (op_i == CIPH_FWD) ? aes_mvm(mask_i, A2X) :
                           (op_i == CIPH_INV) ? aes_mvm(mask_i, S2X) :
                                                aes_mvm(mask_i, A2X);

  // Do the inversion in normal basis X.
  aes_dom_inverse_gf2p8 #(
    .PipelineMul ( PipelineMul )
  ) u_aes_dom_inverse_gf2p8 (
    .clk_i   ( clk_i            ),
    .rst_ni  ( rst_ni           ),
    .we_i    ( we               ),
    .a_y     ( in_data_basis_x  ), // input
    .b_y     ( in_mask_basis_x  ), // input
    .prd_i   ( in_prd           ), // input
    .a_y_inv ( out_data_basis_x ), // output
    .b_y_inv ( out_mask_basis_x ), // output
    .prd_o   ( out_prd          )  // output
  );

  // Convert data to basis S or A.
  assign data_o = (op_i == CIPH_FWD) ? (aes_mvm(out_data_basis_x, X2S) ^ 8'h63) :
                  (op_i == CIPH_INV) ? (aes_mvm(out_data_basis_x, X2A))         :
                                       (aes_mvm(out_data_basis_x, X2S) ^ 8'h63);

  // Convert mask to basis S or A.
  // The addition of constant 8'h63 following the affine transformation is skipped.
  assign mask_o = (op_i == CIPH_FWD) ? aes_mvm(out_mask_basis_x, X2S) :
                  (op_i == CIPH_INV) ? aes_mvm(out_mask_basis_x, X2A) :
                                       aes_mvm(out_mask_basis_x, X2S);

  // Counter register
  logic [2:0] count_d, count_q;
  assign count_d = (out_req_o && out_ack_i) ? '0             :
                   out_req_o                ? count_q        :
                   en_i                     ? count_q + 3'd1 : count_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_count
    if (!rst_ni) begin
      count_q <= '0;
    end else begin
      count_q <= count_d;
    end
  end
  assign out_req_o = en_i & count_q == 3'd4;

  // Write enable signals for internal registers
  assign we[0] = en_i & count_q == 3'd0;
  assign we[1] = en_i & count_q == 3'd1;
  assign we[2] = en_i & count_q == 3'd2;
  assign we[3] = en_i & count_q == 3'd3;

  // Buffer and forward PRD for the individual stages. We get 8 bits from the PRNG for usage in the
  // first cycle. Stages 2, 3 and 4 are driven by other S-Box instances.
  assign prd1_d = we[0] ? prd_i[7:0] : prd1_q;
  prim_flop #(
    .Width      ( 8  ),
    .ResetValue ( '0 )
  ) u_prim_flop_prd1_q (
    .clk_i  ( clk_i  ),
    .rst_ni ( rst_ni ),
    .d_i    ( prd1_d ),
    .q_o    ( prd1_q )
  );
  assign in_prd = '{prd_1: prd1_d,
                    prd_2: prd_i[11:8],
                    prd_3: prd_i[19:12],
                    prd_4: prd_i[27:20]};
  assign prd_o = {out_prd.prd_3, out_prd.prd_2, out_prd.prd_1};

endmodule
