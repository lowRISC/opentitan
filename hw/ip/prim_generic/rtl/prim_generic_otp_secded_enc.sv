// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Hamming SECDED Encoder for OTP emulation.

module prim_generic_otp_secded_enc (
  input        [15:0]    data_i,
  output logic [21:0] data_o
);

  always_comb begin : p_encode
    // data bits are just looped through
    data_o = 22'(data_i);

    // ECC bit computation
    data_o[16] = ^(22'b0000001000111100100011 & data_o);
    data_o[17] = ^(22'b0000000111000101110001 & data_o);
    data_o[18] = ^(22'b0000000010010111011010 & data_o);
    data_o[19] = ^(22'b0000001111100000001110 & data_o);
    data_o[20] = ^(22'b0000000001101011101100 & data_o);
    data_o[21] = ^(22'b0000001100011010010101 & data_o);
  end

endmodule : prim_generic_otp_secded_enc

