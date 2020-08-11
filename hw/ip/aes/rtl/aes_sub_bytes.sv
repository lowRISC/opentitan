// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES SubBytes

module aes_sub_bytes
import aes_pkg::*;
#(
    parameter sbox_impl_e SBoxImpl = SBoxImplLut
) (
    input  ciph_op_e                 op_i,
    input  logic     [3:0][3:0][7:0] data_i,
    input  logic     [3:0][3:0][7:0] in_mask_i,
    input  logic     [3:0][3:0][7:0] out_mask_i,
    output logic     [3:0][3:0][7:0] data_o
);

  // Individually substitute bytes
  for (genvar j = 0; j < 4; j++) begin : gen_sbox_j
    for (genvar i = 0; i < 4; i++) begin : gen_sbox_i
      aes_sbox #(
          .SBoxImpl(SBoxImpl)
      ) u_aes_sbox_ij (
          .op_i      (op_i),
          .data_i    (data_i[i][j]),
          .in_mask_i (in_mask_i[i][j]),
          .out_mask_i(out_mask_i[i][j]),
          .data_o    (data_o[i][j])
      );
    end
  end

endmodule
