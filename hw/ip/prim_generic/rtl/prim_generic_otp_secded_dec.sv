// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Hamming SECDED Encoder for OTP emulation.

module prim_generic_otp_secded_dec (
  input        [21:0] data_i,
  output logic [15:0] data_o,
  output logic [5:0] syndrome_o,
  output logic [1:0] err_o
);

  // Syndrome decoder
  assign syndrome_o[0] = ^(22'b0000011000111100100011 & data_i);
  assign syndrome_o[1] = ^(22'b0000100111000101110001 & data_i);
  assign syndrome_o[2] = ^(22'b0001000010010111011010 & data_i);
  assign syndrome_o[3] = ^(22'b0010001111100000001110 & data_i);
  assign syndrome_o[4] = ^(22'b0100000001101011101100 & data_i);
  assign syndrome_o[5] = ^(22'b1000001100011010010101 & data_i);

  // Correct data bits
  assign data_o[0] = data_i[0] ^ (syndrome_o == 6'd35);
  assign data_o[1] = data_i[1] ^ (syndrome_o == 6'd13);
  assign data_o[2] = data_i[2] ^ (syndrome_o == 6'd56);
  assign data_o[3] = data_i[3] ^ (syndrome_o == 6'd28);
  assign data_o[4] = data_i[4] ^ (syndrome_o == 6'd38);
  assign data_o[5] = data_i[5] ^ (syndrome_o == 6'd19);
  assign data_o[6] = data_i[6] ^ (syndrome_o == 6'd22);
  assign data_o[7] = data_i[7] ^ (syndrome_o == 6'd52);
  assign data_o[8] = data_i[8] ^ (syndrome_o == 6'd7);
  assign data_o[9] = data_i[9] ^ (syndrome_o == 6'd49);
  assign data_o[10] = data_i[10] ^ (syndrome_o == 6'd37);
  assign data_o[11] = data_i[11] ^ (syndrome_o == 6'd25);
  assign data_o[12] = data_i[12] ^ (syndrome_o == 6'd26);
  assign data_o[13] = data_i[13] ^ (syndrome_o == 6'd14);
  assign data_o[14] = data_i[14] ^ (syndrome_o == 6'd42);
  assign data_o[15] = data_i[15] ^ (syndrome_o == 6'd41);

  // err_o calc. bit0: single error, bit1: double error
  logic single_error;
  assign single_error = ^syndrome_o;
  assign err_o[0] =  single_error;
  assign err_o[1] = ~single_error & (|syndrome_o);

endmodule : prim_generic_otp_secded_dec

