// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon SBox unprotected implementation

module prim_ascon_sbox (
  output logic [4:0] state_o,
  input  logic [4:0] state_i
);

  logic [4:0] temp_w [4];

  assign temp_w[0] = state_i;
  assign temp_w[1] = {temp_w[0][3] ^ temp_w[0][4],
                      temp_w[0][3],
                      temp_w[0][1] ^ temp_w[0][2],
                      temp_w[0][1],
                      temp_w[0][0] ^ temp_w[0][4]
                      };
  assign temp_w[2] = {temp_w[1][4] ^ ((~temp_w[1][0]) & temp_w[1][1]),
                      temp_w[1][3] ^ ((~temp_w[1][4]) & temp_w[1][0]),
                      temp_w[1][2] ^ ((~temp_w[1][3]) & temp_w[1][4]),
                      temp_w[1][1] ^ ((~temp_w[1][2]) & temp_w[1][3]),
                      temp_w[1][0] ^ ((~temp_w[1][1]) & temp_w[1][2])
                      };
  assign temp_w[3] = {temp_w[2][4],
                      temp_w[2][3] ^ temp_w[2][2],
                      ~temp_w[2][2],
                      temp_w[2][1] ^ temp_w[2][0],
                      temp_w[2][0] ^ temp_w[2][4]
                      };
  assign state_o = temp_w[3];

endmodule
