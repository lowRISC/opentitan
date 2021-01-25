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
module prim_generic_otp_secded_enc (
  input        [${data_width-1}:0]    data_i,
  output logic [${encoded_width-1}:0] data_o
);

  always_comb begin : p_encode
    // data bits are just looped through
    data_o = ${encoded_width}'(data_i);

    // ECC bit computation
% for i, fanin_mask in enumerate(lc_st_enc.config['secded']['ecc_masks']):
    data_o[${i + data_width}] = ^(${format_str.format(fanin_mask)} & data_o);
% endfor
  end

endmodule : prim_generic_otp_secded_enc

