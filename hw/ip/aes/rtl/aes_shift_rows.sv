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

  // Row 0 is left untouched
  assign data_o[0]  = data_i[0];
  assign data_o[4]  = data_i[4];
  assign data_o[8]  = data_i[8];
  assign data_o[12] = data_i[12];

  // Row 2 does not depend on mode_i
  assign data_o[2]  = data_i[10];
  assign data_o[6]  = data_i[14];
  assign data_o[10] = data_i[2];
  assign data_o[14] = data_i[6];

  // Rows 1 and 3
  always_comb begin : shift_row_1_3
    if (mode_i == AES_ENC) begin
      // Row 1
      data_o[1]  = data_i[5];
      data_o[5]  = data_i[9];
      data_o[9]  = data_i[13];
      data_o[13] = data_i[1];
      // Row 3
      data_o[3]  = data_i[15];
      data_o[7]  = data_i[3];
      data_o[11] = data_i[7];
      data_o[15] = data_i[11];
    end else begin
      // Row 1
      data_o[1]  = data_i[13];
      data_o[5]  = data_i[1];
      data_o[9]  = data_i[5];
      data_o[13] = data_i[9];
      // Row 3
      data_o[3]  = data_i[7];
      data_o[7]  = data_i[11];
      data_o[11] = data_i[15];
      data_o[15] = data_i[3];
    end
  end

endmodule
