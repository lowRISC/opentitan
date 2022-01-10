// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES Masked Canright SBox without Mask Re-Use
//
// For details, see the following paper:
// Canright, "A very compact 'perfectly masked' S-box for AES (corrected)"
// available at https://eprint.iacr.org/2009/011.pdf
//
// Note: This module implements the original masked inversion algorithm without re-using masks.
// For details, see Section 2.2 of the paper. In addition, a formal analysis using REBECCA (stable
// mode) shows that the intermediate masks cannot be created by re-using bits from the input and
// output masks. Instead, fresh random bits need to be used for these intermediate masks. Still,
// the implmentation cannot be made to pass formal analysis in transient mode. It's usage is thus
// discouraged. It's included here mainly for reference.
//
// For details on the REBECCA tool, see the following paper:
// Bloem, "Formal verification of masked hardware implementations in the presence of glitches"
// available at https://eprint.iacr.org/2017/897.pdf

///////////////////////////////////////////////////////////////////////////////////////////////////
// IMPORTANT NOTE:                                                                               //
//                            DO NOT USE THIS FOR SYNTHESIS BLINDLY!                             //
//                                                                                               //
// This implementation relies on primitive cells like prim_buf containing tool-specific          //
// synthesis attributes to enforce the correct ordering of operations and avoid aggressive       //
// optimization. Without the proper primitives, synthesis tools might heavily optimize the       //
// design. The result is likely insecure. Use with care.                                         //
///////////////////////////////////////////////////////////////////////////////////////////////////

// Masked inverse in GF(2^4), using normal basis [z^4, z]
// (see Formulas 6, 13, 14, 15, 16, 17 in the paper)
module aes_masked_inverse_gf2p4_noreuse (
  input  logic [3:0] b,
  input  logic [3:0] q,
  input  logic [1:0] r,
  input  logic [3:0] t,
  output logic [3:0] b_inv
);

  import aes_pkg::*;
  import aes_sbox_canright_pkg::*;

  logic [1:0] b1, b0, q1, q0, c_inv, r_sq, t1, t0;
  assign b1 = b[3:2];
  assign b0 = b[1:0];
  assign q1 = q[3:2];
  assign q0 = q[1:0];
  assign t1 = t[3:2];
  assign t0 = t[1:0];

  ////////////////
  // Formula 13 //
  ////////////////
  // IMPORTANT: The following ops must be executed in order (left to right):
  // c = r ^ aes_scale_omega2_gf2p2(aes_square_gf2p2(b1 ^ b0))
  //       ^ aes_scale_omega2_gf2p2(aes_square_gf2p2(q1 ^ q0))
  //       ^ aes_mul_gf2p2(b1, b0)
  //       ^ aes_mul_gf2p2(b1, q0) ^ aes_mul_gf2p2(b0, q1) ^ aes_mul_gf2p2(q1, q0);

  // Get intermediate terms.
  logic [1:0] scale_omega2_b, scale_omega2_q;
  logic [1:0] mul_b1_b0, mul_b1_q0, mul_b0_q1, mul_q1_q0;
  assign scale_omega2_b = aes_scale_omega2_gf2p2(aes_square_gf2p2(b1 ^ b0));
  assign scale_omega2_q = aes_scale_omega2_gf2p2(aes_square_gf2p2(q1 ^ q0));
  assign mul_b1_b0 = aes_mul_gf2p2(b1, b0);
  assign mul_b1_q0 = aes_mul_gf2p2(b1, q0);
  assign mul_b0_q1 = aes_mul_gf2p2(b0, q1);
  assign mul_q1_q0 = aes_mul_gf2p2(q1, q0);

  // These terms are added to other terms that depend on the same inputs.
  // Avoid aggressive synthesis optimizations.
  logic [1:0] scale_omega2_b_buf, scale_omega2_q_buf;
  prim_buf #(
    .Width ( 4 )
  ) u_prim_buf_scale_omega2_bq (
    .in_i  ( {scale_omega2_b,     scale_omega2_q}     ),
    .out_o ( {scale_omega2_b_buf, scale_omega2_q_buf} )
  );
  logic [1:0] mul_b1_b0_buf, mul_b1_q0_buf, mul_b0_q1_buf, mul_q1_q0_buf;
  prim_buf #(
    .Width ( 8 )
  ) u_prim_buf_mul_bq01 (
    .in_i  ( {mul_b1_b0,     mul_b1_q0,     mul_b0_q1,     mul_q1_q0}     ),
    .out_o ( {mul_b1_b0_buf, mul_b1_q0_buf, mul_b0_q1_buf, mul_q1_q0_buf} )
  );

  // Generate c step by step.
  logic [1:0] c [6];
  logic [1:0] c_buf [6];
  assign c[0] = r        ^ scale_omega2_b_buf;
  assign c[1] = c_buf[0] ^ scale_omega2_q_buf;
  assign c[2] = c_buf[1] ^ mul_b1_b0_buf;
  assign c[3] = c_buf[2] ^ mul_b1_q0_buf;
  assign c[4] = c_buf[3] ^ mul_b0_q1_buf;
  assign c[5] = c_buf[4] ^ mul_q1_q0_buf;

  // Avoid aggressive synthesis optimizations.
  for (genvar i = 0; i < 6; i++) begin : gen_c_buf
    prim_buf #(
      .Width ( 2 )
    ) u_prim_buf_c_i (
      .in_i  ( c[i]     ),
      .out_o ( c_buf[i] )
    );
  end

  ////////////////////////
  // Formulas 14 and 15 //
  ////////////////////////
  // Note: aes_square_gf2p2 contains no logic, it's just a bit swap. There is no need to insert
  // additional buffers to stop aggressive synthesis optimizations here.
  assign c_inv = aes_square_gf2p2(c_buf[5]);
  assign r_sq  = aes_square_gf2p2(r);

  ////////////////////////
  // Formulas 16 and 17 //
  ////////////////////////
  // IMPORTANT: The following ops must be executed in order (left to right):
  // b1_inv = t1 ^ aes_mul_gf2p2(b0, c_inv)
  //             ^ aes_mul_gf2p2(b0, r_sq) ^ aes_mul_gf2p2(q0, c_inv) ^ aes_mul_gf2p2(q0, r_sq);
  // b0_inv = t0 ^ aes_mul_gf2p2(b1, c_inv)
  //             ^ aes_mul_gf2p2(b1, r_sq) ^ aes_mul_gf2p2(q1, c_inv) ^ aes_mul_gf2p2(q1, r_sq);

  // Get intermediate terms.
  logic [1:0] mul_b0_r_sq, mul_q0_c_inv, mul_q0_r_sq;
  logic [1:0] mul_b1_r_sq, mul_q1_c_inv, mul_q1_r_sq;
  assign mul_b0_r_sq  = aes_mul_gf2p2(b0, r_sq);
  assign mul_q0_c_inv = aes_mul_gf2p2(q0, c_inv);
  assign mul_q0_r_sq  = aes_mul_gf2p2(q0, r_sq);
  assign mul_b1_r_sq  = aes_mul_gf2p2(b1, r_sq);
  assign mul_q1_c_inv = aes_mul_gf2p2(q1, c_inv);
  assign mul_q1_r_sq  = aes_mul_gf2p2(q1, r_sq);

  // The multiplier outputs are added to terms that depend on the same inputs.
  // Avoid aggressive synthesis optimizations.
  logic [1:0] mul_b0_r_sq_buf, mul_q0_c_inv_buf, mul_q0_r_sq_buf;
  prim_buf #(
    .Width ( 6 )
  ) u_prim_buf_mul_bq0 (
    .in_i  ( {mul_b0_r_sq,     mul_q0_c_inv,     mul_q0_r_sq}     ),
    .out_o ( {mul_b0_r_sq_buf, mul_q0_c_inv_buf, mul_q0_r_sq_buf} )
  );
  logic [1:0] mul_b1_r_sq_buf, mul_q1_c_inv_buf, mul_q1_r_sq_buf;
  prim_buf #(
    .Width ( 6 )
  ) u_prim_buf_mul_bq1 (
    .in_i  ( {mul_b1_r_sq,     mul_q1_c_inv,     mul_q1_r_sq}     ),
    .out_o ( {mul_b1_r_sq_buf, mul_q1_c_inv_buf, mul_q1_r_sq_buf} )
  );

  // Generate b1_inv and b0_inv step by step.
  logic [1:0] b1_inv [4];
  logic [1:0] b1_inv_buf [4];
  logic [1:0] b0_inv [4];
  logic [1:0] b0_inv_buf [4];
  assign b1_inv[0] = t1            ^ aes_mul_gf2p2(b0, c_inv); // t1 does not depend on b0, c_inv.
  assign b1_inv[1] = b1_inv_buf[0] ^ mul_b0_r_sq_buf;
  assign b1_inv[2] = b1_inv_buf[1] ^ mul_q0_c_inv_buf;
  assign b1_inv[3] = b1_inv_buf[2] ^ mul_q0_r_sq_buf;
  assign b0_inv[0] = t0            ^ aes_mul_gf2p2(b1, c_inv); // t0 does not depend on b1, c_inv.
  assign b0_inv[1] = b0_inv_buf[0] ^ mul_b1_r_sq_buf;
  assign b0_inv[2] = b0_inv_buf[1] ^ mul_q1_c_inv_buf;
  assign b0_inv[3] = b0_inv_buf[2] ^ mul_q1_r_sq_buf;

  // Avoid aggressive synthesis optimizations.
  for (genvar i = 0; i < 4; i++) begin : gen_a01_inv_buf
    prim_buf #(
      .Width ( 2 )
    ) u_prim_buf_b1_inv_i (
      .in_i  ( b1_inv[i]     ),
      .out_o ( b1_inv_buf[i] )
    );
    prim_buf #(
      .Width ( 2 )
    ) u_prim_buf_b0_inv_i (
      .in_i  ( b0_inv[i]     ),
      .out_o ( b0_inv_buf[i] )
    );
  end

  // Note: b_inv is masked by t, b was masked by q.
  assign b_inv = {b1_inv_buf[3], b0_inv_buf[3]};

endmodule

// Masked inverse in GF(2^8), using normal basis [y^16, y]
// (see Formulas 3, 12, 18 and 19 in the paper)
module aes_masked_inverse_gf2p8_noreuse (
  input  logic [7:0] a,    // input data masked by m
  input  logic [7:0] m,    // input mask
  input  logic [7:0] n,    // output mask
  input  logic [9:0] prd,  // pseudo-random data, e.g. for intermediate masks
  output logic [7:0] a_inv // output data masked by n
);

  import aes_pkg::*;
  import aes_sbox_canright_pkg::*;

  logic [3:0] a1, a0, m1, m0, q, b_inv, s1, s0, t;
  logic [1:0] r;

  assign a1 = a[7:4];
  assign a0 = a[3:0];
  assign m1 = m[7:4];
  assign m0 = m[3:0];

  ////////////////////
  // Notes on masks //
  ////////////////////
  // The paper states the following.
  // r:
  // - must be independent of q,
  // - it is suggested to re-use bits of m,
  // - but further analysis shows that this is not sufficient (see below).
  //
  // q:
  // - must be independent of m.
  //
  // t:
  // - must be independent of r,
  // - must be independent of m (for the final steps involving s),
  // - t1 must be independent of q0, t0 must be independent of q1,
  // - it is suggested to use t = q,
  // - but further analysis shows that this is not sufficient (see below).
  //
  // s:
  // - must be independent of t,
  // - s1 must be independent of m0, s0 must be independent of m1,
  // - it is suggested to use s = m,
  // - but further analysis shows that this is not sufficient (see below).
  //
  // Formally analyzing the implementation with REBECCA reveals that:
  // 1. Fresh random bits are required for r, q and t. Any re-use of other mask bits from m or n
  //    causes the static check to fail.
  // 2. s can be the specified output mask n.
  assign r  = prd[1:0];
  assign q  = prd[5:2];
  assign t  = prd[9:6];
  assign s1 = n[7:4];
  assign s0 = n[3:0];

  ////////////////
  // Formula 12 //
  ////////////////
  // IMPORTANT: The following ops must be executed in order (left to right):
  // b = q ^ aes_square_scale_gf2p4_gf2p2(a1 ^ a0)
  //       ^ aes_square_scale_gf2p4_gf2p2(m1 ^ m0)
  //       ^ aes_mul_gf2p4(a1, a0)
  //       ^ aes_mul_gf2p4(a1, m0) ^ aes_mul_gf2p4(a0, m1) ^ aes_mul_gf2p4(m0, m1);

  // Get intermediate terms.
  logic [3:0] ss_a1_a0, ss_m1_m0;
  assign ss_a1_a0 = aes_square_scale_gf2p4_gf2p2(a1 ^ a0);
  assign ss_m1_m0 = aes_square_scale_gf2p4_gf2p2(m1 ^ m0);

  logic [3:0] mul_a1_a0, mul_a1_m0, mul_a0_m1, mul_m0_m1;
  assign mul_a1_a0 = aes_mul_gf2p4(a1, a0);
  assign mul_a1_m0 = aes_mul_gf2p4(a1, m0);
  assign mul_a0_m1 = aes_mul_gf2p4(a0, m1);
  assign mul_m0_m1 = aes_mul_gf2p4(m0, m1);

  // The multiplier outputs are added to terms that depend on the same inputs.
  // Avoid aggressive synthesis optimizations.
  logic [3:0] mul_a1_a0_buf, mul_a1_m0_buf, mul_a0_m1_buf, mul_m0_m1_buf;
  prim_buf #(
    .Width ( 16 )
  ) u_prim_buf_mul_am01 (
    .in_i  ( {mul_a1_a0,     mul_a1_m0,     mul_a0_m1,     mul_m0_m1}     ),
    .out_o ( {mul_a1_a0_buf, mul_a1_m0_buf, mul_a0_m1_buf, mul_m0_m1_buf} )
  );

  // Generate b step by step.
  logic [3:0] b [6];
  logic [3:0] b_buf [6];
  assign b[0] = q        ^ ss_a1_a0; // q does not depend on a1, a0.
  assign b[1] = b_buf[0] ^ ss_m1_m0; // b[0] does not depend on m1, m0.
  assign b[2] = b_buf[1] ^ mul_a1_a0_buf;
  assign b[3] = b_buf[2] ^ mul_a1_m0_buf;
  assign b[4] = b_buf[3] ^ mul_a0_m1_buf;
  assign b[5] = b_buf[4] ^ mul_m0_m1_buf;

  // Avoid aggressive synthesis optimizations.
  for (genvar i = 0; i < 6; i++) begin : gen_b_buf
    prim_buf #(
      .Width ( 4 )
    ) u_prim_buf_b_i (
      .in_i  ( b[i]     ),
      .out_o ( b_buf[i] )
    );
  end

  //////////////////////
  // GF(2^4) Inverter //
  //////////////////////

  // b is masked by q, b_inv is masked by t.
  aes_masked_inverse_gf2p4_noreuse u_aes_masked_inverse_gf2p4 (
    .b     ( b_buf[5] ),
    .q     ( q        ),
    .r     ( r        ),
    .t     ( t        ),
    .b_inv ( b_inv    )
  );

  // The output of the inverse over GF(2^4) and signals derived from that are again recombined
  // with inputs to the GF(2^4) inverter. Aggressive synthesis optimizations across the GF(2^4)
  // inverter may result in SCA leakage and should be avoided.
  logic [3:0] b_inv_buf;
  prim_buf #(
    .Width ( 4 )
  ) u_prim_buf_b_inv (
    .in_i  ( b_inv     ),
    .out_o ( b_inv_buf )
  );

  ////////////////////////
  // Formulas 18 and 19 //
  ////////////////////////
  // IMPORTANT: The following ops must be executed in order (left to right):
  // a1_inv = s1 ^ aes_mul_gf2p4(a0, b_inv)
  //             ^ aes_mul_gf2p4(a0, t) ^ aes_mul_gf2p4(m0, b_inv) ^ aes_mul_gf2p4(m0, t);
  // a0_inv = s0 ^ aes_mul_gf2p4(a1, b_inv)
  //             ^ aes_mul_gf2p4(a1, t) ^ aes_mul_gf2p4(m1, b_inv) ^ aes_mul_gf2p4(m1, t);

  // Get intermediate terms.
  logic [3:0] mul_a0_b_inv, mul_a0_t, mul_m0_b_inv, mul_m0_t;
  logic [3:0] mul_a1_b_inv, mul_a1_t, mul_m1_b_inv, mul_m1_t;
  assign mul_a0_b_inv = aes_mul_gf2p4(a0, b_inv_buf);
  assign mul_a0_t     = aes_mul_gf2p4(a0, t);
  assign mul_m0_b_inv = aes_mul_gf2p4(m0, b_inv_buf);
  assign mul_m0_t     = aes_mul_gf2p4(m0, t);
  assign mul_a1_b_inv = aes_mul_gf2p4(a1, b_inv_buf);
  assign mul_a1_t     = aes_mul_gf2p4(a1, t);
  assign mul_m1_b_inv = aes_mul_gf2p4(m1, b_inv_buf);
  assign mul_m1_t     = aes_mul_gf2p4(m1, t);

  // The multiplier outputs are added to terms that depend on the same inputs.
  // Avoid aggressive synthesis optimizations.
  logic [3:0] mul_a0_b_inv_buf, mul_a0_t_buf, mul_m0_b_inv_buf, mul_m0_t_buf;
  prim_buf #(
    .Width ( 16 )
  ) u_prim_buf_mul_am0 (
    .in_i  ( {mul_a0_b_inv,     mul_a0_t,     mul_m0_b_inv,     mul_m0_t}     ),
    .out_o ( {mul_a0_b_inv_buf, mul_a0_t_buf, mul_m0_b_inv_buf, mul_m0_t_buf} )
  );
  logic [3:0] mul_a1_b_inv_buf, mul_a1_t_buf, mul_m1_b_inv_buf, mul_m1_t_buf;
  prim_buf #(
    .Width ( 16 )
  ) u_prim_buf_mul_am1 (
    .in_i  ( {mul_a1_b_inv,     mul_a1_t,     mul_m1_b_inv,     mul_m1_t}     ),
    .out_o ( {mul_a1_b_inv_buf, mul_a1_t_buf, mul_m1_b_inv_buf, mul_m1_t_buf} )
  );

  // Generate a1_inv and a0_inv step by step.
  logic [3:0] a1_inv [4];
  logic [3:0] a1_inv_buf [4];
  logic [3:0] a0_inv [4];
  logic [3:0] a0_inv_buf [4];
  assign a1_inv[0] = s1            ^ mul_a0_b_inv_buf;
  assign a1_inv[1] = a1_inv_buf[0] ^ mul_a0_t_buf;
  assign a1_inv[2] = a1_inv_buf[1] ^ mul_m0_b_inv_buf;
  assign a1_inv[3] = a1_inv_buf[2] ^ mul_m0_t_buf;
  assign a0_inv[0] = s0            ^ mul_a1_b_inv_buf;
  assign a0_inv[1] = a0_inv_buf[0] ^ mul_a1_t_buf;
  assign a0_inv[2] = a0_inv_buf[1] ^ mul_m1_b_inv_buf;
  assign a0_inv[3] = a0_inv_buf[2] ^ mul_m1_t_buf;

  // Avoid aggressive synthesis optimizations.
  for (genvar i = 0; i < 4; i++) begin : gen_a01_inv_buf
    prim_buf #(
      .Width ( 4 )
    ) u_prim_buf_a1_inv_i (
      .in_i  ( a1_inv[i]     ),
      .out_o ( a1_inv_buf[i] )
    );
    prim_buf #(
      .Width ( 4 )
    ) u_prim_buf_a0_inv_i (
      .in_i  ( a0_inv[i]     ),
      .out_o ( a0_inv_buf[i] )
    );
  end

  // Note: a_inv is masked by s (= n), a was masked by m.
  assign a_inv = {a1_inv_buf[3], a0_inv_buf[3]};

endmodule

// SEC_CM: KEY.MASKING
module aes_sbox_canright_masked_noreuse (
  input  aes_pkg::ciph_op_e op_i,
  input  logic        [7:0] data_i, // masked, the actual input data is data_i ^ mask_i
  input  logic        [7:0] mask_i, // input mask, independent from actual input data
  input  logic       [17:0] prd_i,  // pseudo-random data, for remasking and for intermediate
                                    // masks, must be independent of input mask
  output logic        [7:0] data_o, // masked, the actual output data is data_o ^ mask_o
  output logic        [7:0] mask_o  // output mask
);

  import aes_pkg::*;
  import aes_sbox_canright_pkg::*;

  //////////////////////////
  // Masked Canright SBox //
  //////////////////////////

  logic [7:0] in_data_basis_x, out_data_basis_x;
  logic [7:0] in_mask_basis_x, out_mask_basis_x;

  // Convert data to normal basis X.
  assign in_data_basis_x = (op_i == CIPH_FWD) ? aes_mvm(data_i, A2X)         :
                           (op_i == CIPH_INV) ? aes_mvm(data_i ^ 8'h63, S2X) :
                                                aes_mvm(data_i, A2X);

  // For the masked Canright SBox with no re-use, the output mask directly corresponds to the
  // LSBs of the pseduo-random data provided as input.
  assign mask_o = prd_i[7:0];

  // The remaining bits are used for intermediate masks.
  logic [9:0] prd_masking;
  assign prd_masking = prd_i[17:8];

  // Convert masks to normal basis X.
  // The addition of constant 8'h63 following the affine transformation is skipped.
  assign in_mask_basis_x  = (op_i == CIPH_FWD) ? aes_mvm(mask_i, A2X) :
                            (op_i == CIPH_INV) ? aes_mvm(mask_i, S2X) :
                                                 aes_mvm(mask_i, A2X);

  // The output mask is converted in the opposite direction.
  assign out_mask_basis_x = (op_i == CIPH_INV) ? aes_mvm(mask_o, A2X) :
                            (op_i == CIPH_FWD) ? aes_mvm(mask_o, S2X) :
                                                 aes_mvm(mask_o, S2X);

  // Do the inversion in normal basis X.
  aes_masked_inverse_gf2p8_noreuse u_aes_masked_inverse_gf2p8 (
    .a     ( in_data_basis_x  ), // input
    .m     ( in_mask_basis_x  ), // input
    .n     ( out_mask_basis_x ), // input
    .prd   ( prd_masking      ), // input
    .a_inv ( out_data_basis_x )  // output
  );

  // Convert to basis S or A.
  assign data_o = (op_i == CIPH_FWD) ? (aes_mvm(out_data_basis_x, X2S) ^ 8'h63) :
                  (op_i == CIPH_INV) ? (aes_mvm(out_data_basis_x, X2A))         :
                                       (aes_mvm(out_data_basis_x, X2S) ^ 8'h63);

endmodule
