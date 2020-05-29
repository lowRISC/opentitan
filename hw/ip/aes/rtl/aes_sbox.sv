// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES SBox

module aes_sbox #(
  parameter SBoxImpl = "lut"
) (
  input  aes_pkg::ciph_op_e op_i,
  input  logic [7:0]        data_i,
  output logic [7:0]        data_o
);

  if (SBoxImpl == "lut") begin : gen_sbox_lut
    aes_sbox_lut aes_sbox (
      .op_i,
      .data_i,
      .data_o
    );
  end else if (SBoxImpl == "canright") begin : gen_sbox_canright
    aes_sbox_canright aes_sbox (
      .op_i,
      .data_i,
      .data_o
    );
  end else begin : gen_sbox_masked
    // TODO: Use non-constant masks + remove corresponding comment in aes.sv.
    // See https://github.com/lowRISC/opentitan/issues/1005
    logic [7:0] in_data_m, out_data_m;
    logic [7:0] in_mask, out_mask;
    assign in_mask  = 8'hAA;
    assign out_mask = 8'h55;

    // Mask input data
    assign in_data_m = data_i ^ in_mask;
    if (SBoxImpl == "canright_masked_noreuse") begin : gen_sbox_canright_masked_noreuse
      aes_sbox_canright_masked_noreuse aes_sbox (
        .op_i,
        .data_i     ( in_data_m  ),
        .in_mask_i  ( in_mask    ),
        .out_mask_i ( out_mask   ),
        .data_o     ( out_data_m )
      );
    end else if (SBoxImpl == "canright_masked") begin : gen_sbox_canright_masked
      aes_sbox_canright_masked aes_sbox (
        .op_i,
        .data_i     ( in_data_m  ),
        .in_mask_i  ( in_mask    ),
        .out_mask_i ( out_mask   ),
        .data_o     ( out_data_m )
      );
    end
    // Unmask output data
    assign data_o = out_data_m ^ out_mask;
  end

endmodule
