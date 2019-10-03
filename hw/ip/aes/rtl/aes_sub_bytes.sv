// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES SubBytes

module aes_sub_bytes (
  input  aes_pkg::mode_e mode_i,
  input  logic [7:0]     data_i [16],
  output logic [7:0]     data_o [16]
);

  // Individually substitute bytes
  for (genvar i = 0; i < 16; i++) begin : gen_sbox
    aes_sbox_lut aes_sbox_i (
      .mode_i ( mode_i    ),
      .data_i ( data_i[i] ),
      .data_o ( data_o[i] )
    );
  end

endmodule
