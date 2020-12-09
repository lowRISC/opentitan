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
// For details, see Section 2.2 of the paper. In addition, a formal analysis using REBECCA (static
// mode) shows that the intermediate masks cannot be created by re-using bits from the input and
// output masks. Instead, fresh random bits need to be used for these intermediate masks.
//
// For details on the REBECCA tool, see the following paper:
// Bloem, "Formal verification of masked hardware implementations in the presence of glitches"
// available at https://eprint.iacr.org/2017/897.pdf

///////////////////////////////////////////////////////////////////////////////////////////////////
// IMPORTANT NOTE:                                                                               //
//                            DO NOT USE THIS FOR SYNTHESIS BLINDLY!                             //
//                                                                                               //
// This implementation targets primarily Xilinx Vivado synthesis as well as RTL simulation. It   //
// contains synthesis attributes specific to Xilinx Vivado to enforce the correct ordering of    //
// operations and avoid aggressive optimization. Other synthesis tools might still heavily       //
// optimize the design. The result is likely insecure. Use with care.                            //
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

  logic [1:0] b1, b0, q1, q0, c, c_inv, r_sq, t1, t0, b1_inv, b0_inv;
  assign b1 = b[3:2];
  assign b0 = b[1:0];
  assign q1 = q[3:2];
  assign q0 = q[1:0];
  assign t1 = t[3:2];
  assign t0 = t[1:0];

  // Formula 13
  // IMPORTANT: The following ops must be executed in order (left to right):
  // c = r ^ aes_scale_omega2_gf2p2(aes_square_gf2p2(b1 ^ b0))
  //       ^ aes_scale_omega2_gf2p2(aes_square_gf2p2(q1 ^ q0))
  //       ^ aes_mul_gf2p2(b1, b0)
  //       ^ aes_mul_gf2p2(b1, q0) ^ aes_mul_gf2p2(b0, q1) ^ aes_mul_gf2p2(q1, q0);
  //
  // Get intermediate terms. The terms they are added to depend on the same inputs.
  // Avoid aggressive synthesis optimizations.
  (* keep = "true" *) logic [1:0] scale_omega2_b, scale_omega2_q;
  (* keep = "true" *) logic [1:0] mul_b1_b0, mul_b1_q0, mul_b0_q1, mul_q1_q0;
  assign scale_omega2_b = aes_scale_omega2_gf2p2(aes_square_gf2p2(b1 ^ b0));
  assign scale_omega2_q = aes_scale_omega2_gf2p2(aes_square_gf2p2(q1 ^ q0));
  assign mul_b1_b0 = aes_mul_gf2p2(b1, b0);
  assign mul_b1_q0 = aes_mul_gf2p2(b1, q0);
  assign mul_b0_q1 = aes_mul_gf2p2(b0, q1);
  assign mul_q1_q0 = aes_mul_gf2p2(q1, q0);

  // Generate c step by step.
  (* keep = "true" *) logic [1:0] c_0, c_1, c_2, c_3, c_4;
  assign c_0 = r   ^ scale_omega2_b;
  assign c_1 = c_0 ^ scale_omega2_q;
  assign c_2 = c_1 ^ mul_b1_b0;
  assign c_3 = c_2 ^ mul_b1_q0;
  assign c_4 = c_3 ^ mul_b0_q1;
  assign c   = c_4 ^ mul_q1_q0;

  // Formulas 14 and 15
  assign c_inv = aes_square_gf2p2(c);
  assign r_sq  = aes_square_gf2p2(r);

  // Formulas 16 and 17
  // IMPORTANT: The following ops must be executed in order (left to right):
  // b1_inv = t1 ^ aes_mul_gf2p2(b0, c_inv)
  //             ^ aes_mul_gf2p2(b0, r_sq) ^ aes_mul_gf2p2(q0, c_inv) ^ aes_mul_gf2p2(q0, r_sq);
  // b0_inv = t0 ^ aes_mul_gf2p2(b1, c_inv)
  //             ^ aes_mul_gf2p2(b1, r_sq) ^ aes_mul_gf2p2(q1, c_inv) ^ aes_mul_gf2p2(q1, r_sq);
  //
  // Get intermediate terms. The terms they are added to depend on the same inputs.
  // Avoid aggressive synthesis optimizations.
  (* keep = "true" *) logic [1:0] mul_b0_r_sq, mul_q0_c_inv, mul_q0_r_sq;
  (* keep = "true" *) logic [1:0] mul_b1_r_sq, mul_q1_c_inv, mul_q1_r_sq;
  assign mul_b0_r_sq  = aes_mul_gf2p2(b0, r_sq);
  assign mul_q0_c_inv = aes_mul_gf2p2(q0, c_inv);
  assign mul_q0_r_sq  = aes_mul_gf2p2(q0, r_sq);
  assign mul_b1_r_sq  = aes_mul_gf2p2(b1, r_sq);
  assign mul_q1_c_inv = aes_mul_gf2p2(q1, c_inv);
  assign mul_q1_r_sq  = aes_mul_gf2p2(q1, r_sq);

  // Generate b1_inv and b0_inv step by step.
  (* keep = "true" *) logic [1:0] b1_inv_0, b1_inv_1, b1_inv_2;
  (* keep = "true" *) logic [1:0] b0_inv_0, b0_inv_1, b0_inv_2;
  assign b1_inv_0 = t1       ^ aes_mul_gf2p2(b0, c_inv); // t1 does not depend on b0, c_inv.
  assign b1_inv_1 = b1_inv_0 ^ mul_b0_r_sq;
  assign b1_inv_2 = b1_inv_1 ^ mul_q0_c_inv;
  assign b1_inv   = b1_inv_2 ^ mul_q0_r_sq;
  assign b0_inv_0 = t0       ^ aes_mul_gf2p2(b1, c_inv); // t0 does not depend on b1, c_inv.
  assign b0_inv_1 = b0_inv_0 ^ mul_b1_r_sq;
  assign b0_inv_2 = b0_inv_1 ^ mul_q1_c_inv;
  assign b0_inv   = b0_inv_2 ^ mul_q1_r_sq;

  // Note: b_inv is masked by t, b was masked by q.
  assign b_inv = {b1_inv, b0_inv};

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

  logic [3:0] a1, a0, m1, m0, q, s1, s0, t, a1_inv, a0_inv;
  logic [1:0] r;

  // The output of the inverse over GF(2^4) and signals derived from that are again recombined
  // with inputs to the GF(2^4) inverter. Aggressive synthesis optimizations across the GF(2^4)
  // inverter may result in SCA leakage and should be avoided.
  (* keep = "true" *) logic [3:0] b, b_inv;

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

  // Formula 12
  // IMPORTANT: The following ops must be executed in order (left to right):
  // b = q ^ aes_square_scale_gf2p4_gf2p2(a1 ^ a0)
  //       ^ aes_square_scale_gf2p4_gf2p2(m1 ^ m0)
  //       ^ aes_mul_gf2p4(a1, a0)
  //       ^ aes_mul_gf2p4(a1, m0) ^ aes_mul_gf2p4(a0, m1) ^ aes_mul_gf2p4(m0, m1);
  //
  // Get intermediate terms. The terms they are added to depend on the same inputs.
  // Avoid aggressive synthesis optimizations.
  (* keep = "true" *) logic [3:0] mul_a1_a0, mul_a1_m0, mul_a0_m1, mul_m0_m1;
  assign mul_a1_a0 = aes_mul_gf2p4(a1, a0);
  assign mul_a1_m0 = aes_mul_gf2p4(a1, m0);
  assign mul_a0_m1 = aes_mul_gf2p4(a0, m1);
  assign mul_m0_m1 = aes_mul_gf2p4(m0, m1);
  // Generate b step by step.
  (* keep = "true" *) logic [3:0] b_0, b_1, b_2, b_3, b_4;
  assign b_0 = q   ^ aes_square_scale_gf2p4_gf2p2(a1 ^ a0); // q does not depend on a1, a0.
  assign b_1 = b_0 ^ aes_square_scale_gf2p4_gf2p2(m1 ^ m0); // b_0 does not depend on m1, m0.
  assign b_2 = b_1 ^ mul_a1_a0;
  assign b_3 = b_2 ^ mul_a1_m0;
  assign b_4 = b_3 ^ mul_a0_m1;
  assign b   = b_4 ^ mul_m0_m1;

  // b is masked by q, b_inv is masked by t.
  aes_masked_inverse_gf2p4_noreuse aes_masked_inverse_gf2p4 (
    .b     ( b     ),
    .q     ( q     ),
    .r     ( r     ),
    .t     ( t     ),
    .b_inv ( b_inv )
  );

  // Formulas 18 and 19
  // IMPORTANT: The following ops must be executed in order (left to right):
  // a1_inv = s1 ^ aes_mul_gf2p4(a0, b_inv)
  //             ^ aes_mul_gf2p4(a0, t) ^ aes_mul_gf2p4(m0, b_inv) ^ aes_mul_gf2p4(m0, t);
  // a0_inv = s0 ^ aes_mul_gf2p4(a1, b_inv)
  //             ^ aes_mul_gf2p4(a1, t) ^ aes_mul_gf2p4(m1, b_inv) ^ aes_mul_gf2p4(m1, t);
  //
  // Get intermediate terms. The terms they are added to depend on the same inputs.
  // Avoid aggressive synthesis optimizations.
  (* keep = "true" *) logic [3:0] mul_a0_b_inv, mul_a0_t, mul_m0_b_inv, mul_m0_t;
  (* keep = "true" *) logic [3:0] mul_a1_b_inv, mul_a1_t, mul_m1_b_inv, mul_m1_t;
  assign mul_a0_b_inv = aes_mul_gf2p4(a0, b_inv);
  assign mul_a0_t     = aes_mul_gf2p4(a0, t);
  assign mul_m0_b_inv = aes_mul_gf2p4(m0, b_inv);
  assign mul_m0_t     = aes_mul_gf2p4(m0, t);
  assign mul_a1_b_inv = aes_mul_gf2p4(a1, b_inv);
  assign mul_a1_t     = aes_mul_gf2p4(a1, t);
  assign mul_m1_b_inv = aes_mul_gf2p4(m1, b_inv);
  assign mul_m1_t     = aes_mul_gf2p4(m1, t);

  // Generate a1_inv and a0_inv step by step.
  (* keep = "true" *) logic [3:0] a1_inv_0, a1_inv_1, a1_inv_2;
  (* keep = "true" *) logic [3:0] a0_inv_0, a0_inv_1, a0_inv_2;
  assign a1_inv_0 = s1       ^ mul_a0_b_inv;
  assign a1_inv_1 = a1_inv_0 ^ mul_a0_t;
  assign a1_inv_2 = a1_inv_1 ^ mul_m0_b_inv;
  assign a1_inv   = a1_inv_2 ^ mul_m0_t;
  assign a0_inv_0 = s0       ^ mul_a1_b_inv;
  assign a0_inv_1 = a0_inv_0 ^ mul_a1_t;
  assign a0_inv_2 = a0_inv_1 ^ mul_m1_b_inv;
  assign a0_inv   = a0_inv_2 ^ mul_m1_t;

  // Note: a_inv is masked by s (= n), a was masked by m.
  assign a_inv = {a1_inv, a0_inv};

endmodule

module aes_sbox_canright_masked_noreuse (
  input  aes_pkg::ciph_op_e op_i,
  input  logic [7:0]        data_i,        // masked, the actual input data is data_i ^ in_mask_i
  input  logic [7:0]        in_mask_i,     // input mask, independent from actual input data
  input  logic [7:0]        out_mask_i,    // output mask, independent from input mask
  input  logic [9:0]        prd_masking_i, // pseudo-random data, e.g. for intermediate masks
  output logic [7:0]        data_o         // masked, the actual output data is data_o ^ out_mask_i
);

  import aes_pkg::*;
  import aes_sbox_canright_pkg::*;

  //////////////////////////
  // Masked Canright SBox //
  //////////////////////////

  logic [7:0] in_data_basis_x, out_data_basis_x;
  logic [7:0] in_mask_basis_x, out_mask_basis_x;

  // Convert data to normal basis X.
  assign in_data_basis_x = (op_i == CIPH_FWD) ? aes_mvm(data_i, A2X) :
                                                aes_mvm(data_i ^ 8'h63, S2X);

  // Convert masks to normal basis X.
  // The addition of constant 8'h63 following the affine transformation is skipped.
  assign in_mask_basis_x  = (op_i == CIPH_FWD) ? aes_mvm(in_mask_i, A2X) :
                                                 aes_mvm(in_mask_i, S2X);

  // The output mask is converted in the opposite direction.
  assign out_mask_basis_x = (op_i == CIPH_INV) ? aes_mvm(out_mask_i, A2X) :
                                                 aes_mvm(out_mask_i, S2X);

  // Do the inversion in normal basis X.
  aes_masked_inverse_gf2p8_noreuse aes_masked_inverse_gf2p8 (
    .a     ( in_data_basis_x  ), // input
    .m     ( in_mask_basis_x  ), // input
    .n     ( out_mask_basis_x ), // input
    .prd   ( prd_masking_i    ), // input
    .a_inv ( out_data_basis_x )  // output
  );

  // Convert to basis S or A.
  assign data_o = (op_i == CIPH_FWD) ? (aes_mvm(out_data_basis_x, X2S) ^ 8'h63) :
                                       (aes_mvm(out_data_basis_x, X2A));

endmodule
