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
// For details, see Section 2.2 of the paper.

///////////////////////////////////////////////////////////////////////////////////////////////////
// IMPORTANT NOTE:                                                                               //
//                            DO NOT USE THIS FOR SYNTHESIS BLINDLY!                             //
//                                                                                               //
// This is a high-level implementation targeting primarily RTL simulation. Synthesis tools might //
// heavily optimize the design. The result is likely insecure. Use with care.                    //
///////////////////////////////////////////////////////////////////////////////////////////////////

module aes_sbox_canright_masked_noreuse (
    input aes_pkg::ciph_op_e op_i,
    input logic [7:0] data_i,  // masked, the actual input data is data_i ^ in_mask_i
    input logic [7:0] in_mask_i,  // input mask, independent from actual input data
    input logic [7:0] out_mask_i,  // output mask, independent from input mask
    output logic [7:0] data_o  // masked, the actual output data is data_o ^ out_mask_i
);

  import aes_pkg::*;
  import aes_sbox_canright_pkg::*;

  ///////////////
  // Functions //
  ///////////////

  // Masked inverse in GF(2^4), using normal basis [z^4, z]
  // (see Formulas 6, 13, 14, 15, 16, 17 in the paper)
  function automatic logic [3:0] aes_masked_inverse_gf2p4(logic [3:0] b, logic [3:0] q,
                                                          logic [1:0] r, logic [3:0] t);
    logic [3:0] b_inv;
    logic [1:0] b1, b0, q1, q0, c, c_inv, r_sq, t1, t0, b1_inv, b0_inv;
    b1 = b[3:2];
    b0 = b[1:0];
    q1 = q[3:2];
    q0 = q[1:0];
    t1 = t[3:2];
    t0 = t[1:0];

    // Formula 13
    // IMPORTANT: The following ops must be executed in order (left to right):
    c = r ^ aes_scale_omega2_gf2p2(aes_square_gf2p2(b1 ^ b0)) ^
        aes_scale_omega2_gf2p2(aes_square_gf2p2(q1 ^ q0)) ^ aes_mul_gf2p2(b1, b0) ^
        aes_mul_gf2p2(b1, q0) ^ aes_mul_gf2p2(b0, q1) ^ aes_mul_gf2p2(q1, q0);
    //

    // Formulas 14 and 15
    c_inv = aes_square_gf2p2(c);
    r_sq = aes_square_gf2p2(r);

    // Formulas 16 and 17
    // IMPORTANT: The following ops must be executed in order (left to right):
    b1_inv = t1 ^ aes_mul_gf2p2(b0, c_inv) ^ aes_mul_gf2p2(b0, r_sq) ^ aes_mul_gf2p2(q0, c_inv) ^
        aes_mul_gf2p2(q0, r_sq);
    b0_inv = t0 ^ aes_mul_gf2p2(b1, c_inv) ^ aes_mul_gf2p2(b1, r_sq) ^ aes_mul_gf2p2(q1, c_inv) ^
        aes_mul_gf2p2(q1, r_sq);
    //

    // Note: b_inv is masked by t, b was masked by q.
    b_inv = {b1_inv, b0_inv};

    return b_inv;
  endfunction

  // Masked inverse in GF(2^8), using normal basis [y^16, y]
  // (see Formulas 3, 12, 18 and 19 in the paper)
  function automatic logic [7:0] aes_masked_inverse_gf2p8(logic [7:0] a, logic [7:0] m,
                                                          logic [7:0] n);
    logic [7:0] a_inv;
    logic [3:0] a1, a0, m1, m0, b, b_inv, q, s1, s0, t, a1_inv, a0_inv;
    logic [1:0] r;
    a1 = a[7:4];
    a0 = a[3:0];
    m1 = m[7:4];
    m0 = m[3:0];

    // q must be independent of m.
    q = n[7:4];

    // Formula 12
    // IMPORTANT: The following ops must be executed in order (left to right):
    b = q ^ aes_square_scale_gf2p4_gf2p2(a1 ^ a0) ^ aes_square_scale_gf2p4_gf2p2(m1 ^ m0) ^
        aes_mul_gf2p4(a1, a0) ^ aes_mul_gf2p4(a1, m0) ^ aes_mul_gf2p4(a0, m1) ^
        aes_mul_gf2p4(m1, m0);
    //

    // r must be independent of q.
    r = m1[3:2];

    // Note that the paper states the following requirements on t:
    // - t must be independent of r.
    // - t1 must be independent of q0, t0 must be independent of q1.
    // - t must be independent of m (for the final steps involving s)
    // The paper suggests to use t = q. To select s = n for the output mask (s must be independent
    // of t = q = n[7:4]), we would need t = m0 or similar (not r, m1[3:2] though), but this would
    // break the random product distribution of aes_mul_gf2p4(m0, t), or aes_mul_gf2p4(m1, t) below
    // (see Lemma 2 in the paper). For this reason, we select t = q here and apply a final mask
    // switch from s = m to n after the inversion.
    t = q;

    // b is masked by q, b_inv is masked by t.
    b_inv = aes_masked_inverse_gf2p4(b, q, r, t);

    // Note that the paper states the following requirements on s:
    // - s must be independent of t
    // - s1 must be independent of m0, s0 must be independent of m1.
    // The paper suggests to use s = m (the input mask). To still end up with the specified output
    // mask n, we will apply a final mask switch after the inversion.
    s1 = m1;
    s0 = m0;

    // Formulas 18 and 19
    // IMPORTANT: The following ops must be executed in order (left to right):
    a1_inv = s1 ^ aes_mul_gf2p4(a0, b_inv) ^ aes_mul_gf2p4(a0, t) ^ aes_mul_gf2p4(m0, b_inv) ^
        aes_mul_gf2p4(m0, t);
    a0_inv = s0 ^ aes_mul_gf2p4(a1, b_inv) ^ aes_mul_gf2p4(a1, t) ^ aes_mul_gf2p4(m1, b_inv) ^
        aes_mul_gf2p4(m1, t);
    //

    // Note: a_inv is now masked by s = m, a was masked by m.
    a_inv = {a1_inv, a0_inv};

    // To have a_inv masked by n (the specified output mask), we perform a final mask switch.
    // IMPORTANT: The following ops must be executed in order (left to right):
    a_inv = a_inv ^ n ^ m;
    //

    return a_inv;
  endfunction

  //////////////////////////
  // Masked Canright SBox //
  //////////////////////////

  logic [7:0] data_basis_x, data_inverse;
  logic [7:0] in_mask_basis_x;
  logic [7:0] out_mask_basis_x;

  // Convert data to normal basis X.
  assign data_basis_x = (op_i == CIPH_FWD) ? aes_mvm(data_i, A2X) : aes_mvm(data_i ^ 8'h63, S2X);

  // Convert masks to normal basis X.
  // The addition of constant 8'h63 following the affine transformation is skipped.
  assign in_mask_basis_x = (op_i == CIPH_FWD) ? aes_mvm(in_mask_i, A2X) : aes_mvm(in_mask_i, S2X);

  // The output mask is converted in the opposite direction.
  assign
      out_mask_basis_x = (op_i == CIPH_INV) ? aes_mvm(out_mask_i, A2X) : aes_mvm(out_mask_i, S2X);

  // Do the inversion in normal basis X.
  assign data_inverse = aes_masked_inverse_gf2p8(data_basis_x, in_mask_basis_x, out_mask_basis_x);

  // Convert to basis S or A.
  assign data_o =
      (op_i == CIPH_FWD) ? (aes_mvm(data_inverse, X2S) ^ 8'h63) : (aes_mvm(data_inverse, X2A));

endmodule
