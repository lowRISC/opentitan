// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES ShiftRows

module aes_shift_rows (
  input  aes_pkg::mode_e mode_i,
  input  logic [7:0]     data_i [16],
  output logic [7:0]     data_o [16]
);

  import aes_pkg::*;

  logic [3:0][3:0][7:0] state_i;
  logic [3:0][3:0][7:0] state_o;

  always_comb begin : conv_bytes_1d_to_2d
    for (int i=0; i<4; i++) begin : rows
      for (int j=0; j<4; j++) begin : columns
        state_i[i][j] = data_i[4*j+i];
      end
    end
  end

  // Row 0 is left untouched
  assign state_o[0] = state_i[0];

  // Row 2 does not depend on mode_i
  assign state_o[2] = aes_circ_byte_shift(state_i[2], 2);

  // Row 1
  assign state_o[1] = (mode_i == AES_ENC) ? aes_circ_byte_shift(state_i[1], -1)
                                          : aes_circ_byte_shift(state_i[1],  1);

  // Row 3
  assign state_o[3] = (mode_i == AES_ENC) ? aes_circ_byte_shift(state_i[3],  1)
                                          : aes_circ_byte_shift(state_i[3], -1);

  always_comb begin : conv_bytes_2d_to_1d
    for (int i=0; i<4; i++) begin : rows
      for (int j=0; j<4; j++) begin : columns
        data_o[4*j+i] = state_o[i][j];
      end
    end
  end

endmodule
