// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES mul4 implements a constant multiplication by 4 on GF(2^8).

module aes_mul4 (
  input  logic [7:0] data_i,
  output logic [7:0] data_o
);

  assign data_o[7] = data_i[5];
  assign data_o[6] = data_i[4];
  assign data_o[5] = data_i[3] ^ data_i[7];
  assign data_o[4] = data_i[2] ^ data_i[7] ^ data_i[6];
  assign data_o[3] = data_i[1]             ^ data_i[6];
  assign data_o[2] = data_i[0] ^ data_i[7];
  assign data_o[1] = data_i[7]             ^ data_i[6];
  assign data_o[0] = data_i[6];

endmodule
