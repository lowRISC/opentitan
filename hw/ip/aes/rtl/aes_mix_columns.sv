// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES MixColumns

module aes_mix_columns (
  input  aes_pkg::ciph_op_e    op_i,
  input  logic [3:0][3:0][7:0] data_i,
  output logic [3:0][3:0][7:0] data_o
);

  import aes_pkg::*;

  // Transpose to operate on columns
  logic [3:0][3:0][7:0] data_i_transposed;
  logic [3:0][3:0][7:0] data_o_transposed;

  assign data_i_transposed = aes_transpose(data_i);

  // Individually mix columns
  for (genvar i = 0; i < 4; i++) begin : gen_mix_column
    aes_mix_single_column u_aes_mix_column_i (
      .op_i   ( op_i                 ),
      .data_i ( data_i_transposed[i] ),
      .data_o ( data_o_transposed[i] )
    );
  end

  assign data_o = aes_transpose(data_o_transposed);

endmodule
