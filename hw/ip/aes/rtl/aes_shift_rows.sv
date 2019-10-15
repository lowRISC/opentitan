// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES ShiftRows

module aes_shift_rows (
  input  aes_pkg::mode_e       mode_i,
  input  logic [3:0][3:0][7:0] data_i,
  output logic [3:0][3:0][7:0] data_o
);

  import aes_pkg::*;

  // Row 0 is left untouched
  assign data_o[0] = data_i[0];

  // Row 2 does not depend on mode_i
  assign data_o[2] = aes_circ_byte_shift(data_i[2], 2);

  // Row 1
  assign data_o[1] = (mode_i == AES_ENC) ? aes_circ_byte_shift(data_i[1], -1)
                                         : aes_circ_byte_shift(data_i[1],  1);

  // Row 3
  assign data_o[3] = (mode_i == AES_ENC) ? aes_circ_byte_shift(data_i[3],  1)
                                         : aes_circ_byte_shift(data_i[3], -1);

endmodule
