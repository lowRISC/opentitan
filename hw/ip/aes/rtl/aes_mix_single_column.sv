// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES MixColumns for one single column of the state matrix
//
// For details, see Equations 4-7 of:
// Satoh et al., "A Compact Rijndael Hardware Architecture with S-Box Optimization"

module aes_mix_single_column (
  input  aes_pkg::ciph_op_e op_i,
  input  logic [3:0][7:0]   data_i,
  output logic [3:0][7:0]   data_o
);

  import aes_pkg::*;

  logic [3:0][7:0] x;
  logic [1:0][7:0] y;
  logic [1:0][7:0] z;

  logic [3:0][7:0] x_mul2;
  logic [1:0][7:0] y_pre_mul4;
  logic      [7:0] y2, y2_pre_mul2;

  logic [1:0][7:0] z_muxed;

  // Drive x
  assign x[0] = data_i[0] ^ data_i[3];
  assign x[1] = data_i[3] ^ data_i[2];
  assign x[2] = data_i[2] ^ data_i[1];
  assign x[3] = data_i[1] ^ data_i[0];

  // Mul2(x)
  for (genvar i = 0; i < 4; i++) begin : gen_x_mul2
    assign x_mul2[i] = aes_mul2(x[i]);
  end

  // Drive y_pre_mul4
  assign y_pre_mul4[0] = data_i[3] ^ data_i[1];
  assign y_pre_mul4[1] = data_i[2] ^ data_i[0];

  // Mul4(y_pre_mul4)
  for (genvar i = 0; i < 2; i++) begin : gen_mul4
    assign y[i] = aes_mul4(y_pre_mul4[i]);
  end

  // Drive y2_pre_mul2
  assign y2_pre_mul2 = y[0] ^ y[1];

  // Mul2(y)
  assign y2 = aes_mul2(y2_pre_mul2);

  // Drive z
  assign z[0] = y2 ^ y[0];
  assign z[1] = y2 ^ y[1];

  // Mux z
  assign z_muxed[0] = (op_i == CIPH_FWD) ? 8'b0 :
                      (op_i == CIPH_INV) ? z[0] : 8'b0;
  assign z_muxed[1] = (op_i == CIPH_FWD) ? 8'b0 :
                      (op_i == CIPH_INV) ? z[1] : 8'b0;

  // Drive outputs
  assign data_o[0] = data_i[1] ^ x_mul2[3] ^ x[1] ^ z_muxed[1];
  assign data_o[1] = data_i[0] ^ x_mul2[2] ^ x[1] ^ z_muxed[0];
  assign data_o[2] = data_i[3] ^ x_mul2[1] ^ x[3] ^ z_muxed[1];
  assign data_o[3] = data_i[2] ^ x_mul2[0] ^ x[3] ^ z_muxed[0];

endmodule
