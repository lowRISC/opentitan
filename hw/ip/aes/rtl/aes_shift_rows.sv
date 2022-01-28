// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES ShiftRows

module aes_shift_rows (
  input  aes_pkg::ciph_op_e    op_i,
  input  logic [3:0][3:0][7:0] data_i,
  output logic [3:0][3:0][7:0] data_o
);

  import aes_pkg::*;

  // Row 0 is left untouched
  assign data_o[0] = data_i[0];

  // Row 2 does not depend on op_i
  assign data_o[2] = aes_circ_byte_shift(data_i[2], 2'h2);

  // Row 1
  assign data_o[1] = (op_i == CIPH_FWD) ? aes_circ_byte_shift(data_i[1], 2'h3) :
                     (op_i == CIPH_INV) ? aes_circ_byte_shift(data_i[1], 2'h1) :
                                          aes_circ_byte_shift(data_i[1], 2'h3);

  // Row 3
  assign data_o[3] = (op_i == CIPH_FWD) ? aes_circ_byte_shift(data_i[3], 2'h1) :
                     (op_i == CIPH_INV) ? aes_circ_byte_shift(data_i[3], 2'h3) :
                                          aes_circ_byte_shift(data_i[3], 2'h1);

endmodule
