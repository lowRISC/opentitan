// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES Masked Canright SBox with Mask Re-Use
//
// For details, see the following paper:
// Canright, "A very compact 'perfectly masked' S-box for AES (corrected)"
// available at https://eprint.iacr.org/2009/011.pdf
//
// Note: This module implements the masked inversion algorithm with re-using masks.
// For details, see Section 2.3 of the paper. Re-using masks may make the implementation more
// vulnerable to higher-order differential side-channel analysis, but it remains secure against
// first-order attacks. This implementation is commonly referred to as THE Canright Masked SBox.

///////////////////////////////////////////////////////////////////////////////////////////////////
// IMPORTANT NOTE:                                                                               //
//                            DO NOT USE THIS FOR SYNTHESIS BLINDLY!                             //
//                                                                                               //
// This is a high-level implementation targeting primarily RTL simulation. Synthesis tools might //
// heavily optimize the design. The result is likely insecure. Use with care.                    //
///////////////////////////////////////////////////////////////////////////////////////////////////

module aes_sbox_canright_masked (
  input  aes_pkg::ciph_op_e op_i,
  input  logic [7:0]        data_i,     // masked, the actual input data is data_i ^ in_mask_i
  input  logic [7:0]        in_mask_i,  // input mask, independent from actual input data
  input  logic [7:0]        out_mask_i, // output mask, independent from input mask
  output logic [7:0]        data_o      // masked, the actual output data is data_o ^ out_mask_i
);

  import aes_pkg::*;
  import aes_sbox_canright_pkg::*;

  ///////////////
  // Functions //
  ///////////////

  // Masked inverse in GF(2^4), using normal basis [z^4, z]
  // (see Formulas 6, 13, 14, 15, 21, 22, 23, 24 in the paper)
  function automatic logic [3:0] aes_masked_inverse_gf2p4(logic [3:0] b,
                                                          logic [3:0] q,
                                                          logic [1:0] r,
                                                          logic [3:0] m1);
    logic [3:0] b_inv;
    logic [1:0] b1, b0, q1, q0, c, c_inv, c2_inv, r_sq, m11, m10, b1_inv, b0_inv;
    logic [1:0] mul_b0_q1, mul_b1_q0, mul_q0_q1;
    b1  = b[3:2];
    b0  = b[1:0];
    q1  = q[3:2];
    q0  = q[1:0];
    m11 = m1[3:2];
    m10 = m1[1:0];

    // Get re-usable intermediate results.
    mul_b0_q1 = aes_mul_gf2p2(b0, q1);
    mul_b1_q0 = aes_mul_gf2p2(b1, q0);
    mul_q0_q1 = aes_mul_gf2p2(q0, q1);

    // Formula 13
    // IMPORTANT: The following ops must be executed in order (left to right):
    c = r ^ aes_scale_omega2_gf2p2(aes_square_gf2p2(b1 ^ b0))
          ^ aes_scale_omega2_gf2p2(aes_square_gf2p2(q1 ^ q0))
          ^ aes_mul_gf2p2(b1, b0)
          ^ aes_mul_gf2p2(b1, q0) ^ mul_b0_q1 ^ mul_q0_q1;
    //

    // Formulas 14 and 15
    c_inv = aes_square_gf2p2(c);
    r_sq  = aes_square_gf2p2(r);

    // Re-masking c_inv
    // Formulas 21 and 23
    // IMPORTANT: First combine the masks (ops in parens) then apply to c_inv:
    c_inv  = c_inv ^ (q1 ^ r_sq);
    c2_inv = c_inv ^ (q0 ^ q1);
    //

    // Formulas 22 and 24
    // IMPORTANT: The following ops must be executed in order (left to right):
    b1_inv = m11 ^ aes_mul_gf2p2(b0, c_inv)
                 ^ mul_b0_q1 ^ aes_mul_gf2p2(q0, c_inv)  ^ mul_q0_q1;
    b0_inv = m10 ^ aes_mul_gf2p2(b1, c2_inv)
                 ^ mul_b1_q0 ^ aes_mul_gf2p2(q1, c2_inv) ^ mul_q0_q1;
    //

    // Note: b_inv is masked by m1, b was masked by q.
    b_inv = {b1_inv, b0_inv};

    return b_inv;
  endfunction

  // Masked inverse in GF(2^8), using normal basis [y^16, y]
  // (see Formulas 3, 12, 25, 26 and 27 in the paper)
  function automatic logic [7:0] aes_masked_inverse_gf2p8(logic [7:0] a,
                                                          logic [7:0] m,
                                                          logic [7:0] n);
    logic [7:0] a_inv;
    logic [3:0] a1, a0, m1, m0, b, b_inv, b2_inv, q, s1, s0, a1_inv, a0_inv;
    logic [3:0] mul_a0_m1, mul_a1_m0, mul_m0_m1;
    logic [1:0] r;
    a1 = a[7:4];
    a0 = a[3:0];
    m1 = m[7:4];
    m0 = m[3:0];

    // Get re-usable intermediate results.
    mul_a0_m1 = aes_mul_gf2p4(a0, m1);
    mul_a1_m0 = aes_mul_gf2p4(a1, m0);
    mul_m0_m1 = aes_mul_gf2p4(m0, m1);

    // q must be independent of m.
    q = n[7:4];

    // Formula 12
    // IMPORTANT: The following ops must be executed in order (left to right):
    b = q ^ aes_square_scale_gf2p4_gf2p2(a1 ^ a0)
          ^ aes_square_scale_gf2p4_gf2p2(m1 ^ m0)
          ^ aes_mul_gf2p4(a1, a0)
          ^ mul_a1_m0 ^ mul_a0_m1 ^ mul_m0_m1;
    //

    // r must be independent of q.
    r = m1[3:2];

    // b is masked by q, b_inv is masked by m1.
    b_inv = aes_masked_inverse_gf2p4(b, q, r, m1);

    // Formula 26
    // IMPORTANT: First combine the masks (ops in parens) then apply to b_inv:
    b2_inv = b_inv ^ (m1 ^ m0);
    //

    // s is the specified output mask n.
    s1 = n[7:4];
    s0 = n[3:0];

    // Formulas 25 and 27
    // IMPORTANT: The following ops must be executed in order (left to right):
    a1_inv = s1 ^ aes_mul_gf2p4(a0, b_inv)
                ^ mul_a0_m1 ^ aes_mul_gf2p4(m0, b_inv)  ^ mul_m0_m1;
    a0_inv = s0 ^ aes_mul_gf2p4(a1, b2_inv)
                ^ mul_a1_m0 ^ aes_mul_gf2p4(m1, b2_inv) ^ mul_m0_m1;
    //

    // Note: a_inv is now masked by s = n, a was masked by m.
    a_inv = {a1_inv, a0_inv};

    return a_inv;
  endfunction

  //////////////////////////
  // Masked Canright SBox //
  //////////////////////////

  logic [7:0] data_basis_x, data_inverse;
  logic [7:0] in_mask_basis_x;
  logic [7:0] out_mask_basis_x;

  // Convert data to normal basis X.
  assign data_basis_x = (op_i == CIPH_FWD) ? aes_mvm(data_i, A2X) :
                                             aes_mvm(data_i ^ 8'h63, S2X);

  // Convert masks to normal basis X.
  // The addition of constant 8'h63 following the affine transformation is skipped.
  assign in_mask_basis_x  = (op_i == CIPH_FWD) ? aes_mvm(in_mask_i, A2X) :
                                                 aes_mvm(in_mask_i, S2X);

  // The output mask is converted in the opposite direction.
  assign out_mask_basis_x = (op_i == CIPH_INV) ? aes_mvm(out_mask_i, A2X) :
                                                 aes_mvm(out_mask_i, S2X);

  // Do the inversion in normal basis X.
  assign data_inverse = aes_masked_inverse_gf2p8(data_basis_x, in_mask_basis_x, out_mask_basis_x);

  // Convert to basis S or A.
  assign data_o = (op_i == CIPH_FWD) ? (aes_mvm(data_inverse, X2S) ^ 8'h63) :
                                       (aes_mvm(data_inverse, X2A));

endmodule
