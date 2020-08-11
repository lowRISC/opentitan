// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES SBox

module aes_sbox
import aes_pkg::*;
#(
    parameter sbox_impl_e SBoxImpl = SBoxImplLut
) (
    input  ciph_op_e       op_i,
    input  logic     [7:0] data_i,
    input  logic     [7:0] in_mask_i,
    input  logic     [7:0] out_mask_i,
    output logic     [7:0] data_o
);

  import aes_pkg::*;
  localparam bit SBoxMasked = (SBoxImpl == SBoxImplCanrightMasked ||
                               SBoxImpl == SBoxImplCanrightMaskedNoreuse) ? 1'b1 : 1'b0;

  if (!SBoxMasked) begin : gen_sbox_unmasked
    // Tie off unused mask inputs.
    logic [15:0] unused_masks;
    assign unused_masks = {in_mask_i, out_mask_i};

    if (SBoxImpl == SBoxImplCanright) begin : gen_sbox_canright
      aes_sbox_canright u_aes_sbox (
          .op_i,
          .data_i,
          .data_o
      );
    end else begin : gen_sbox_lut  // SBoxImpl == SBoxImplLut
      aes_sbox_lut u_aes_sbox (
          .op_i,
          .data_i,
          .data_o
      );
    end
  end else begin : gen_sbox_masked

    if (SBoxImpl == SBoxImplCanrightMaskedNoreuse) begin : gen_sbox_canright_masked_noreuse
      aes_sbox_canright_masked_noreuse u_aes_sbox (
          .op_i,
          .data_i,
          .in_mask_i,
          .out_mask_i,
          .data_o
      );
    end else begin : gen_sbox_canright_masked  // SBoxImpl == SBoxImplCanrightMasked
      aes_sbox_canright_masked u_aes_sbox (
          .op_i,
          .data_i,
          .in_mask_i,
          .out_mask_i,
          .data_o
      );
    end
  end

endmodule
