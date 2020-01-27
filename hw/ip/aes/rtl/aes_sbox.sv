// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES SBox

module aes_sbox #(
  parameter SBoxImpl = "lut"
) (
  input  aes_pkg::ciph_op_e op_i,
  input  logic [7:0]        data_i,
  output logic [7:0]        data_o
);

  if (SBoxImpl == "lut") begin : gen_sbox_lut
    aes_sbox_lut aes_sbox (
      .op_i,
      .data_i,
      .data_o
    );
  end else if (SBoxImpl == "canright") begin : gen_sbox_canright
    aes_sbox_canright aes_sbox (
      .op_i,
      .data_i,
      .data_o
    );
  end

endmodule
