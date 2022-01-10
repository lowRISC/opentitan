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
//
// A formal analysis using REBECCA (stable and transient mode) shows that this implementation is
// not secure. It's usage is thus discouraged. It's included here mainly for reference.
//
// For details on the REBECCA tool, see the following paper:
// Bloem, "Formal verification of masked hardware implementations in the presence of glitches"
// available at https://eprint.iacr.org/2017/897.pdf

///////////////////////////////////////////////////////////////////////////////////////////////////
// IMPORTANT NOTE:                                                                               //
//                            DO NOT USE THIS FOR SYNTHESIS BLINDLY!                             //
//                                                                                               //
// This implementation relies on primitive cells like prim_buf/xor2 containing tool-specific     //
// synthesis attributes to enforce the correct ordering of operations and avoid aggressive       //
// optimization. Without the proper primitives, synthesis tools might heavily optimize the       //
// design. The result is likely insecure. Use with care.                                         //
///////////////////////////////////////////////////////////////////////////////////////////////////

// Masked inverse in GF(2^4), using normal basis [z^4, z]
// (see Formulas 6, 13, 14, 15, 21, 22, 23, 24 in the paper)
module aes_masked_inverse_gf2p4 (
  input  logic [3:0] b,
  input  logic [3:0] q,
  input  logic [1:0] r,
  input  logic [3:0] m1,
  output logic [3:0] b_inv
);

  import aes_pkg::*;
  import aes_sbox_canright_pkg::*;

  logic [1:0] b1, b0, q1, q0, c_inv, r_sq, m11, m10;
  assign b1  = b[3:2];
  assign b0  = b[1:0];
  assign q1  = q[3:2];
  assign q0  = q[1:0];
  assign m11 = m1[3:2];
  assign m10 = m1[1:0];

  // Get re-usable intermediate results.
  logic [1:0] mul_b0_q1, mul_b1_q0, mul_q1_q0;
  assign mul_b0_q1 = aes_mul_gf2p2(b0, q1);
  assign mul_b1_q0 = aes_mul_gf2p2(b1, q0);
  assign mul_q1_q0 = aes_mul_gf2p2(q1, q0);

  // Avoid aggressive synthesis optimizations.
  logic [1:0] mul_b0_q1_buf, mul_b1_q0_buf, mul_q1_q0_buf;
  prim_buf #(
    .Width ( 6 )
  ) u_prim_buf_mul_bq01 (
    .in_i  ( {mul_b0_q1,     mul_b1_q0,     mul_q1_q0}     ),
    .out_o ( {mul_b0_q1_buf, mul_b1_q0_buf, mul_q1_q0_buf} )
  );

  ////////////////
  // Formula 13 //
  ////////////////
  // IMPORTANT: The following ops must be executed in order (left to right):
  // c = r ^ aes_scale_omega2_gf2p2(aes_square_gf2p2(b1 ^ b0))
  //       ^ aes_scale_omega2_gf2p2(aes_square_gf2p2(q1 ^ q0))
  //       ^ aes_mul_gf2p2(b1, b0)
  //       ^ mul_b1_q0 ^ mul_b0_q1 ^ mul_q0_q1;

  // Get intermediate terms.
  logic [1:0] scale_omega2_b, scale_omega2_q;
  logic [1:0] mul_b1_b0;
  assign scale_omega2_b = aes_scale_omega2_gf2p2(aes_square_gf2p2(b1 ^ b0));
  assign scale_omega2_q = aes_scale_omega2_gf2p2(aes_square_gf2p2(q1 ^ q0));
  assign mul_b1_b0 = aes_mul_gf2p2(b1, b0);

  // These terms are added to other terms that depend on the same inputs.
  // Avoid aggressive synthesis optimizations.
  logic [1:0] scale_omega2_b_buf, scale_omega2_q_buf;
  prim_buf #(
    .Width ( 4 )
  ) u_prim_buf_scale_omega2_bq (
    .in_i  ( {scale_omega2_b,     scale_omega2_q}     ),
    .out_o ( {scale_omega2_b_buf, scale_omega2_q_buf} )
  );
  logic [1:0] mul_b1_b0_buf;
  prim_buf #(
    .Width ( 2 )
  ) u_prim_buf_mul_b1_b0 (
    .in_i  ( mul_b1_b0     ),
    .out_o ( mul_b1_b0_buf )
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
  // Formulas 21 and 23 //
  ////////////////////////
  // Re-masking c_inv
  // IMPORTANT: First combine the masks (ops in parens) then apply to c_inv:
  // c_inv  = c_inv ^ (q1 ^ r_sq);
  // c2_inv = c_inv ^ (q0 ^ q1);

  // Get intermediate terms.
  logic [1:0] xor_q1_r_sq, xor_q0_q1, c1_inv, c2_inv;
  prim_xor2 #(
    .Width ( 2 )
  ) u_prim_xor_q1_r_sq (
    .in0_i ( q1          ),
    .in1_i ( r_sq        ),
    .out_o ( xor_q1_r_sq )
  );
  prim_xor2 #(
    .Width ( 2 )
  ) u_prim_xor_q0_q1 (
    .in0_i ( q0        ),
    .in1_i ( q1        ),
    .out_o ( xor_q0_q1 )
  );

  // Generate c1_inv and c2_inv.
  prim_xor2 #(
    .Width ( 2 )
  ) u_prim_c1_inv (
    .in0_i ( xor_q1_r_sq ),
    .in1_i ( c_inv       ),
    .out_o ( c1_inv      )
  );
  prim_xor2 #(
    .Width ( 2 )
  ) u_prim_c2_inv (
    .in0_i ( c1_inv    ),
    .in1_i ( xor_q0_q1 ),
    .out_o ( c2_inv    )
  );

  ////////////////////////
  // Formulas 22 and 24 //
  ////////////////////////
  // IMPORTANT: The following ops must be executed in order (left to right):
  // b1_inv = m11 ^ aes_mul_gf2p2(b0, c1_inv)
  //              ^ mul_b0_q1 ^ aes_mul_gf2p2(q0, c1_inv) ^ mul_q0_q1;
  // b0_inv = m10 ^ aes_mul_gf2p2(b1, c2_inv)
  //              ^ mul_b1_q0 ^ aes_mul_gf2p2(q1, c2_inv) ^ mul_q0_q1;

  // Get intermediate terms.
  logic [1:0] mul_b0_c1_inv, mul_q0_c1_inv, mul_b1_c2_inv, mul_q1_c2_inv;
  assign mul_b0_c1_inv = aes_mul_gf2p2(b0, c1_inv);
  assign mul_q0_c1_inv = aes_mul_gf2p2(q0, c1_inv);
  assign mul_b1_c2_inv = aes_mul_gf2p2(b1, c2_inv);
  assign mul_q1_c2_inv = aes_mul_gf2p2(q1, c2_inv);

  // The multiplier outputs are added to terms that depend on the same inputs.
  // Avoid aggressive synthesis optimizations.
  logic [1:0] mul_b0_c1_inv_buf, mul_q0_c1_inv_buf, mul_b1_c2_inv_buf, mul_q1_c2_inv_buf;
  prim_buf #(
    .Width ( 8 )
  ) u_prim_buf_mul_bq01_c12_inv (
    .in_i  ( {mul_b0_c1_inv,     mul_q0_c1_inv,     mul_b1_c2_inv,     mul_q1_c2_inv}     ),
    .out_o ( {mul_b0_c1_inv_buf, mul_q0_c1_inv_buf, mul_b1_c2_inv_buf, mul_q1_c2_inv_buf} )
  );

  // Generate b1_inv and b0_inv step by step.
  logic [1:0] b1_inv [4];
  logic [1:0] b1_inv_buf [4];
  logic [1:0] b0_inv [4];
  logic [1:0] b0_inv_buf [4];
  assign b1_inv[0] = m11           ^ mul_b0_c1_inv_buf;
  assign b1_inv[1] = b1_inv_buf[0] ^ mul_b0_q1_buf;
  assign b1_inv[2] = b1_inv_buf[1] ^ mul_q0_c1_inv_buf;
  assign b1_inv[3] = b1_inv_buf[2] ^ mul_q1_q0_buf;
  assign b0_inv[0] = m10           ^ mul_b1_c2_inv_buf;
  assign b0_inv[1] = b0_inv_buf[0] ^ mul_b1_q0_buf;
  assign b0_inv[2] = b0_inv_buf[1] ^ mul_q1_c2_inv_buf;
  assign b0_inv[3] = b0_inv_buf[2] ^ mul_q1_q0_buf;

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

  // Note: b_inv is masked by m1, b was masked by q.
  assign b_inv = {b1_inv_buf[3], b0_inv_buf[3]};
endmodule

// Masked inverse in GF(2^8), using normal basis [y^16, y]
// (see Formulas 3, 12, 25, 26 and 27 in the paper)
module aes_masked_inverse_gf2p8 (
  input  logic [7:0] a,
  input  logic [7:0] m,
  input  logic [7:0] n,
  output logic [7:0] a_inv
);

  import aes_pkg::*;
  import aes_sbox_canright_pkg::*;

  logic [3:0] a1, a0, m1, m0, q, b_inv, s1, s0;
  logic [1:0] r;

  assign a1 = a[7:4];
  assign a0 = a[3:0];
  assign m1 = m[7:4];
  assign m0 = m[3:0];

  ////////////////////
  // Notes on masks //
  ////////////////////
  // The paper states the following.
  // - r must be independent of q.
  // - q must be independent of m.
  // - s is the specified output mask n.
  assign r = m1[3:2];
  assign q = n[7:4];
  assign s1 = n[7:4];
  assign s0 = n[3:0];

  // Get re-usable intermediate results.
  logic [3:0] mul_a0_m1, mul_a1_m0, mul_m0_m1;
  assign mul_a0_m1 = aes_mul_gf2p4(a0, m1);
  assign mul_a1_m0 = aes_mul_gf2p4(a1, m0);
  assign mul_m0_m1 = aes_mul_gf2p4(m0, m1);

  // Avoid aggressive synthesis optimizations.
  logic [3:0] mul_a0_m1_buf, mul_a1_m0_buf, mul_m0_m1_buf;
  prim_buf #(
    .Width ( 12 )
  ) u_prim_buf_mul_bq01 (
    .in_i  ( {mul_a0_m1,     mul_a1_m0,     mul_m0_m1}     ),
    .out_o ( {mul_a0_m1_buf, mul_a1_m0_buf, mul_m0_m1_buf} )
  );

  ////////////////
  // Formula 12 //
  ////////////////
  // IMPORTANT: The following ops must be executed in order (left to right):
  // b = q ^ aes_square_scale_gf2p4_gf2p2(a1 ^ a0)
  //       ^ aes_square_scale_gf2p4_gf2p2(m1 ^ m0)
  //       ^ aes_mul_gf2p4(a1, a0)
  //       ^ mul_a1_m0 ^ mul_a0_m1 ^ mul_m0_m1;

  // Get intermediate terms.
  logic [3:0] ss_a1_a0, ss_m1_m0;
  assign ss_a1_a0 = aes_square_scale_gf2p4_gf2p2(a1 ^ a0);
  assign ss_m1_m0 = aes_square_scale_gf2p4_gf2p2(m1 ^ m0);

  logic [3:0] mul_a1_a0;
  assign mul_a1_a0 = aes_mul_gf2p4(a1, a0);

  // The multiplier output is added to terms that depend on the same inputs.
  // Avoid aggressive synthesis optimizations.
  logic [3:0] mul_a1_a0_buf;
  prim_buf #(
    .Width ( 4 )
  ) u_prim_buf_mul_am01 (
    .in_i  ( mul_a1_a0     ),
    .out_o ( mul_a1_a0_buf )
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

  // b is masked by q, b_inv is masked by m1.
  aes_masked_inverse_gf2p4 u_aes_masked_inverse_gf2p4 (
    .b     ( b_buf[5] ),
    .q     ( q        ),
    .r     ( r        ),
    .m1    ( m1       ),
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

  ////////////////
  // Formula 26 //
  ////////////////
  // IMPORTANT: First combine the masks (ops in parens) then apply to b_inv:
  // b2_inv = b_inv ^ (m1 ^ m0);

  // Generate b2_inv step by step.
  logic [3:0] xor_m1_m0, b2_inv;
  prim_xor2 #(
    .Width ( 4 )
  ) u_prim_xor_m1_m0 (
    .in0_i ( m1        ),
    .in1_i ( m0        ),
    .out_o ( xor_m1_m0 )
  );
  prim_xor2 #(
    .Width ( 4 )
  ) u_prim_xor_b2_inv (
    .in0_i ( b_inv_buf ),
    .in1_i ( xor_m1_m0 ),
    .out_o ( b2_inv    )
  );

  ////////////////////////
  // Formulas 25 and 27 //
  ////////////////////////
  // IMPORTANT: The following ops must be executed in order (left to right):
  // a1_inv = s1 ^ aes_mul_gf2p4(a0, b_inv)
  //             ^ mul_a0_m1 ^ aes_mul_gf2p4(m0, b_inv)  ^ mul_m0_m1;
  // a0_inv = s0 ^ aes_mul_gf2p4(a1, b2_inv)
  //             ^ mul_a1_m0 ^ aes_mul_gf2p4(m1, b2_inv) ^ mul_m0_m1;

  // Get intermediate terms.
  logic [3:0] mul_a0_b_inv, mul_m0_b_inv, mul_a1_b2_inv, mul_m1_b2_inv;
  assign mul_a0_b_inv  = aes_mul_gf2p4(a0, b_inv_buf);
  assign mul_m0_b_inv  = aes_mul_gf2p4(m0, b_inv_buf);
  assign mul_a1_b2_inv = aes_mul_gf2p4(a1, b2_inv);
  assign mul_m1_b2_inv = aes_mul_gf2p4(m1, b2_inv);

  // The multiplier outputs are added to terms that depend on the same inputs.
  // Avoid aggressive synthesis optimizations.
  logic [3:0] mul_a0_b_inv_buf, mul_m0_b_inv_buf, mul_a1_b2_inv_buf, mul_m1_b2_inv_buf;
  prim_buf #(
    .Width ( 16 )
  ) u_prim_buf_mul_bq01_c12_inv (
    .in_i  ( {mul_a0_b_inv,     mul_m0_b_inv,     mul_a1_b2_inv,     mul_m1_b2_inv}     ),
    .out_o ( {mul_a0_b_inv_buf, mul_m0_b_inv_buf, mul_a1_b2_inv_buf, mul_m1_b2_inv_buf} )
  );

  // Generate a1_inv and a0_inv step by step.
  logic [3:0] a1_inv [4];
  logic [3:0] a1_inv_buf [4];
  logic [3:0] a0_inv [4];
  logic [3:0] a0_inv_buf [4];
  assign a1_inv[0] = s1            ^ mul_a0_b_inv_buf;
  assign a1_inv[1] = a1_inv_buf[0] ^ mul_a0_m1_buf;
  assign a1_inv[2] = a1_inv_buf[1] ^ mul_m0_b_inv_buf;
  assign a1_inv[3] = a1_inv_buf[2] ^ mul_m0_m1_buf;
  assign a0_inv[0] = s0            ^ mul_a1_b2_inv_buf; // s0 doesn't depend on a1, b2_inv.
  assign a0_inv[1] = a0_inv_buf[0] ^ mul_a1_m0_buf;
  assign a0_inv[2] = a0_inv_buf[1] ^ mul_m1_b2_inv_buf;
  assign a0_inv[3] = a0_inv_buf[2] ^ mul_m0_m1_buf;

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
module aes_sbox_canright_masked (
  input  aes_pkg::ciph_op_e op_i,
  input  logic [7:0]        data_i, // masked, the actual input data is data_i ^ mask_i
  input  logic [7:0]        mask_i, // input mask, independent from actual input data
  input  logic [7:0]        prd_i,  // pseudo-random data for remasking, independent of input mask
  output logic [7:0]        data_o, // masked, the actual output data is data_o ^ mask_o
  output logic [7:0]        mask_o  // output mask
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

  // For the masked Canright SBox, the output mask directly corresponds to the pseduo-random data
  // provided as input.
  assign mask_o = prd_i;

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
  aes_masked_inverse_gf2p8 u_aes_masked_inverse_gf2p8 (
    .a     ( in_data_basis_x  ), // input
    .m     ( in_mask_basis_x  ), // input
    .n     ( out_mask_basis_x ), // input
    .a_inv ( out_data_basis_x )  // output
  );

  // Convert to basis S or A.
  assign data_o = (op_i == CIPH_FWD) ? (aes_mvm(out_data_basis_x, X2S) ^ 8'h63) :
                  (op_i == CIPH_INV) ? (aes_mvm(out_data_basis_x, X2A))         :
                                       (aes_mvm(out_data_basis_x, X2S) ^ 8'h63);

endmodule
