// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES Canright SBox #4
//
// For details, see the technical report: Canright, "A very compact Rijndael S-box"
// available at https://hdl.handle.net/10945/25608

module aes_sbox_canright (
  input  aes_pkg::ciph_op_e op_i,
  input  logic [7:0]        data_i,
  output logic [7:0]        data_o
);

  import aes_pkg::*;
  import aes_sbox_canright_pkg::*;

  ///////////////
  // Functions //
  ///////////////

  // Inverse in GF(2^4), using normal basis [alpha^8, alpha^2]
  // (see Figure 12 in the technical report)
  function automatic logic [3:0] aes_inverse_gf2p4(logic [3:0] gamma);
    logic [3:0] delta;
    logic [1:0] a, b, c, d;
    a          = gamma[3:2] ^ gamma[1:0];
    b          = aes_mul_gf2p2(gamma[3:2], gamma[1:0]);
    c          = aes_scale_omega2_gf2p2(aes_square_gf2p2(a));
    d          = aes_square_gf2p2(c ^ b);
    delta[3:2] = aes_mul_gf2p2(d, gamma[1:0]);
    delta[1:0] = aes_mul_gf2p2(d, gamma[3:2]);
    return delta;
  endfunction

  // Inverse in GF(2^8), using normal basis [d^16, d]
  // (see Figure 11 in the technical report)
  function automatic logic [7:0] aes_inverse_gf2p8(logic [7:0] gamma);
    logic [7:0] delta;
    logic [3:0] a, b, c, d;
    a          = gamma[7:4] ^ gamma[3:0];
    b          = aes_mul_gf2p4(gamma[7:4], gamma[3:0]);
    c          = aes_square_scale_gf2p4_gf2p2(a);
    d          = aes_inverse_gf2p4(c ^ b);
    delta[7:4] = aes_mul_gf2p4(d, gamma[3:0]);
    delta[3:0] = aes_mul_gf2p4(d, gamma[7:4]);
    return delta;
  endfunction

  ///////////////////
  // Canright SBox //
  ///////////////////

  logic [7:0] data_basis_x, data_inverse;

  // Convert to normal basis X.
  assign data_basis_x = (op_i == CIPH_FWD) ? aes_mvm(data_i, A2X)         :
                        (op_i == CIPH_INV) ? aes_mvm(data_i ^ 8'h63, S2X) :
                                             aes_mvm(data_i, A2X);

  // Do the inversion in normal basis X.
  assign data_inverse = aes_inverse_gf2p8(data_basis_x);

  // Convert to basis S or A.
  assign data_o       = (op_i == CIPH_FWD) ? aes_mvm(data_inverse, X2S) ^ 8'h63 :
                        (op_i == CIPH_INV) ? aes_mvm(data_inverse, X2A) :
                                             aes_mvm(data_inverse, X2S) ^ 8'h63;

endmodule
