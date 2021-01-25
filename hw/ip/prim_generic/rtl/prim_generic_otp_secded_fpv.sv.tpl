// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SECDED FPV testbench.
<%
data_width = lc_st_enc.config['secded']['data_width']
ecc_width = lc_st_enc.config['secded']['ecc_width']
encoded_width = data_width + ecc_width
format_str = str(encoded_width) + "'b{:0" + str(encoded_width) + "b}"
%>
module prim_generic_otp_secded_fpv (
  input        [${data_width-1}:0] data_i,
  output logic [${data_width-1}:0] data_o,
  output logic [${ecc_width-1}:0] syndrome_o,
  output logic [1:0] err_o
);

  logic [${encoded_width-1}:0] error_inject, data_enc, data_inj;

  prim_generic_otp_secded_enc prim_generic_otp_secded_enc (
    .data_i,
    .data_o(data_enc)
  );

  assign data_inj = error_inject ^ data;

  prim_generic_otp_secded_dec prim_generic_otp_secded_dec (
    .data_i    (data_inj),
    .data_o,
    .syndrome_o,
    .err_o
  );

  `ASSUME_FPV(SingleError_M, $countones(error_inject) <= 2)
  `ASSERT(SingleErrorDetect_A, $countones(error_inject) == 1 |-> err_o[0])
  `ASSERT(SingleErrorDetectReverse_A, err_o[0] |-> $countones(error_inject) == 1)
  `ASSERT(DoubleErrorDetect_A, $countones(error_inject) == 2 |-> err_o[1])
  `ASSERT(DoubleErrorDetectReverse_A, err_o[1] |-> $countones(error_inject) == 2)
  `ASSERT(SingleErrorCorrect_A, $countones(error_inject) <= 1 |-> data_i == data_o)
   // TODO Add syndrome check

endmodule : prim_generic_otp_secded_fpv

