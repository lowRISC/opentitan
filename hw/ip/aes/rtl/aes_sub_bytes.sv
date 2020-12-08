// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES SubBytes

module aes_sub_bytes import aes_pkg::*;
#(
  parameter sbox_impl_e SBoxImpl = SBoxImplLut
) (
  input  logic                              clk_i,
  input  logic                              rst_ni,
  input  logic                              en_i,
  output logic                              out_req_o,
  input  logic                              out_ack_i,
  input  ciph_op_e                          op_i,
  input  logic              [3:0][3:0][7:0] data_i,
  input  logic              [3:0][3:0][7:0] in_mask_i,
  input  logic              [3:0][3:0][7:0] out_mask_i,
  input  logic [3:0][3:0][WidthPRDSBox-1:0] prd_masking_i,
  output logic              [3:0][3:0][7:0] data_o
);

  logic [3:0][3:0] out_req;

  // Collect REQ signals.
  assign out_req_o = &out_req;

  // Individually substitute bytes.
  for (genvar j = 0; j < 4; j++) begin : gen_sbox_j
    for (genvar i = 0; i < 4; i++) begin : gen_sbox_i
      aes_sbox #(
        .SBoxImpl ( SBoxImpl )
      ) u_aes_sbox_ij (
        .clk_i         ( clk_i               ),
        .rst_ni        ( rst_ni              ),
        .en_i          ( en_i                ),
        .out_req_o     ( out_req[i][j]       ),
        .out_ack_i     ( out_ack_i           ),
        .op_i          ( op_i                ),
        .data_i        ( data_i[i][j]        ),
        .in_mask_i     ( in_mask_i[i][j]     ),
        .out_mask_i    ( out_mask_i[i][j]    ),
        .prd_masking_i ( prd_masking_i[i][j] ),
        .data_o        ( data_o[i][j]        )
      );
    end
  end

endmodule
