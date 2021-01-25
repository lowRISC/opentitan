// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SECDED Encoder for OTP emulation.
<%
data_width = lc_st_enc.config['secded']['data_width']
ecc_width = lc_st_enc.config['secded']['ecc_width']
encoded_width = data_width + ecc_width
format_str = str(encoded_width) + "'b{:0" + str(encoded_width) + "b}"
%>
module prim_generic_otp_secded_dec (
  input        [${encoded_width-1}:0] data_i,
  output logic [${data_width-1}:0] data_o,
  output logic [${ecc_width-1}:0] syndrome_o,
  output logic [1:0] err_o
);

  // Syndrome decoder
% for i, fanin_mask in enumerate(lc_st_enc.config['secded']['ecc_masks']):
  assign syndrome_o[${i}] = ^(${format_str.format(fanin_mask + (1 << (i + data_width)))} & data_i);
% endfor

  // Correct data bits
% for i in range(data_width):
  assign data_o[${i}] = data_i[${i}] ^ (syndrome_o == ${ecc_width}'d${lc_st_enc.config['secded']['syndrome_map'][i]});
% endfor

  // err_o calc. bit0: single error, bit1: double error
  logic single_error;
  assign single_error = ^syndrome_o;
  assign err_o[0] =  single_error;
  assign err_o[1] = ~single_error & (|syndrome_o);

endmodule : prim_generic_otp_secded_dec

