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
  input  sp2v_e                             en_i,
  output sp2v_e                             out_req_o,
  input  sp2v_e                             out_ack_i,
  input  ciph_op_e                          op_i,
  input  logic              [3:0][3:0][7:0] data_i,
  input  logic              [3:0][3:0][7:0] mask_i,
  input  logic [3:0][3:0][WidthPRDSBox-1:0] prd_i,
  output logic              [3:0][3:0][7:0] data_o,
  output logic              [3:0][3:0][7:0] mask_o,
  output logic                              err_o
);

  sp2v_e           en;
  logic            en_err;
  logic [3:0][3:0] out_req;
  sp2v_e           out_ack;
  logic            out_ack_err;

  // Check sparsely encoded signals.
  logic [Sp2VWidth-1:0] en_raw;
  aes_sel_buf_chk #(
    .Num   ( Sp2VNum   ),
    .Width ( Sp2VWidth )
  ) u_aes_sb_en_buf_chk (
    .clk_i  ( clk_i  ),
    .rst_ni ( rst_ni ),
    .sel_i  ( en_i   ),
    .sel_o  ( en_raw ),
    .err_o  ( en_err )
  );
  assign en = sp2v_e'(en_raw);

  logic [Sp2VWidth-1:0] out_ack_raw;
  aes_sel_buf_chk #(
    .Num   ( Sp2VNum   ),
    .Width ( Sp2VWidth )
  ) u_aes_sb_out_ack_buf_chk (
    .clk_i  ( clk_i       ),
    .rst_ni ( rst_ni      ),
    .sel_i  ( out_ack_i   ),
    .sel_o  ( out_ack_raw ),
    .err_o  ( out_ack_err )
  );
  assign out_ack = sp2v_e'(out_ack_raw);

  // Individually substitute bytes.
  for (genvar j = 0; j < 4; j++) begin : gen_sbox_j
    for (genvar i = 0; i < 4; i++) begin : gen_sbox_i
      aes_sbox #(
        .SBoxImpl ( SBoxImpl )
      ) u_aes_sbox_ij (
        .clk_i     ( clk_i                ),
        .rst_ni    ( rst_ni               ),
        .en_i      ( en == SP2V_HIGH      ),
        .out_req_o ( out_req[i][j]        ),
        .out_ack_i ( out_ack == SP2V_HIGH ),
        .op_i      ( op_i                 ),
        .data_i    ( data_i[i][j]         ),
        .mask_i    ( mask_i[i][j]         ),
        .prd_i     ( prd_i [i][j]         ),
        .data_o    ( data_o[i][j]         ),
        .mask_o    ( mask_o[i][j]         )
      );
    end
  end

  // Collect REQ signals.
  assign out_req_o = &out_req ? SP2V_HIGH : SP2V_LOW;

  // Collect encoding errors.
  assign err_o = en_err | out_ack_err;

endmodule
