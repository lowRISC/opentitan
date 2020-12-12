// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Wrapper to allow LEC of masked S-Boxes against LUT-based S-Box.

module aes_sbox_masked_wrapper (
  input  aes_pkg::ciph_op_e op_i,
  input  logic [7:0]        data_i,
  output logic [7:0]        data_o
);

  logic [7:0] in_data_m, out_data_m;
  logic [7:0] in_mask, out_mask;
  logic [9:0] prd_masking;

  // The mask inputs are tied to constant values.
  assign in_mask     = 8'hAA;
  assign out_mask    = 8'h55;
  assign prd_masking = 10'h2AA;

  // Mask input data
  assign in_data_m = data_i ^ in_mask;

  aes_sbox_masked aes_sbox_masked (
    .op_i          ( op_i        ),
    .data_i        ( in_data_m   ),
    .in_mask_i     ( in_mask     ),
    .out_mask_i    ( out_mask    ),
    .prd_masking_i ( prd_masking ),
    .data_o        ( out_data_m  )
  );

  // Unmask output data
  assign data_o = out_data_m ^ out_mask;

endmodule
