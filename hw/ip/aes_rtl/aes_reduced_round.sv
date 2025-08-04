// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// AES reduced round data path
// This module is useful for formal masking verification using e.g. Alma.
// For details, see hw/ip/aes/pre_sca/alma/README.md .

module aes_reduced_round import aes_pkg::*;
#(
  parameter sbox_impl_e SecSBoxImpl = SBoxImplDom
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

  localparam int NumShares = 2;

  // Signals
  logic [3:0][3:0][7:0] sub_bytes_out;
  logic [3:0][3:0][7:0] sb_out_mask;
  logic [3:0][3:0][7:0] shift_rows_in [NumShares];
  logic [3:0][3:0][7:0] shift_rows_out [NumShares];
  logic [3:0][3:0][7:0] mix_columns_out [NumShares];

  // A single reduced (no AddKey) round of the cipher data path
  aes_sub_bytes #(
    .SecSBoxImpl ( SecSBoxImpl )
  ) u_aes_sub_bytes (
    .clk_i     ( clk_i             ),
    .rst_ni    ( rst_ni            ),
    .en_i      ( en_i              ),
    .out_req_o ( out_req_o         ),
    .out_ack_i ( out_ack_i         ),
    .op_i      ( op_i              ),
    .data_i    ( data_i            ),
    .mask_i    ( mask_i            ),
    .prd_i     ( prd_i             ),
    .data_o    ( sub_bytes_out     ),
    .mask_o    ( sb_out_mask       ),
    .err_o     ( err_o             )
  );

  for (genvar s = 0; s < NumShares; s++) begin : gen_shares_shift_mix
    if (s == 0) begin : gen_shift_in_data
      // The (masked) data share
      assign shift_rows_in[s] = sub_bytes_out;
    end else begin : gen_shift_in_mask
      // The mask share
      assign shift_rows_in[s] = sb_out_mask;
    end

    aes_shift_rows u_aes_shift_rows (
      .op_i   ( op_i              ),
      .data_i ( shift_rows_in[s]  ),
      .data_o ( shift_rows_out[s] )
    );

    aes_mix_columns u_aes_mix_columns (
      .op_i   ( op_i               ),
      .data_i ( shift_rows_out[s]  ),
      .data_o ( mix_columns_out[s] )
    );
  end

  // Outputs
  assign data_o = mix_columns_out[0];
  assign mask_o = mix_columns_out[1];

endmodule
