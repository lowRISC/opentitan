// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES SBox

`include "prim_assert.sv"

module aes_sbox import aes_pkg::*;
#(
  parameter sbox_impl_e SBoxImpl = SBoxImplLut
) (
  input  logic                    clk_i,
  input  logic                    rst_ni,
  input  logic                    en_i,
  output logic                    out_req_o,
  input  logic                    out_ack_i,
  input  ciph_op_e                op_i,
  input  logic              [7:0] data_i,
  input  logic              [7:0] mask_i,
  input  logic [WidthPRDSBox-1:0] prd_i,
  output logic              [7:0] data_o,
  output logic              [7:0] mask_o
);

  import aes_pkg::*;
  localparam bit SBoxMasked = (SBoxImpl == SBoxImplCanrightMasked ||
                               SBoxImpl == SBoxImplCanrightMaskedNoreuse ||
                               SBoxImpl == SBoxImplDom) ? 1'b1 : 1'b0;

  localparam bit SBoxSingleCycle = (SBoxImpl == SBoxImplDom) ? 1'b0 : 1'b1;

  if (!SBoxMasked) begin : gen_sbox_unmasked
    // Tie off unused inputs.
    logic                    unused_clk;
    logic                    unused_rst;
    logic              [7:0] unused_mask;
    logic [WidthPRDSBox-1:0] unused_prd;
    assign unused_clk  = clk_i;
    assign unused_rst  = rst_ni;
    assign unused_mask = mask_i;
    assign unused_prd  = prd_i;

    if (SBoxImpl == SBoxImplCanright) begin : gen_sbox_canright
      aes_sbox_canright u_aes_sbox (
        .op_i   ( op_i   ),
        .data_i ( data_i ),
        .data_o ( data_o )
      );

    end else begin : gen_sbox_lut // SBoxImpl == SBoxImplLut
      aes_sbox_lut u_aes_sbox (
        .op_i   ( op_i   ),
        .data_i ( data_i ),
        .data_o ( data_o )
      );
    end

    assign mask_o = '0;

  end else begin : gen_sbox_masked

    if (SBoxImpl == SBoxImplDom) begin : gen_sbox_dom
      // Tie off unused inputs.
      if (WidthPRDSBox > 8) begin : gen_unused_prd
        logic [WidthPRDSBox-1-8:0] unused_prd;
        assign unused_prd = prd_i[WidthPRDSBox-1:8];
      end

      aes_sbox_dom u_aes_sbox (
        .clk_i      ( clk_i      ),
        .rst_ni     ( rst_ni     ),
        .en_i       ( en_i       ),
        .out_req_o  ( out_req_o  ),
        .out_ack_i  ( out_ack_i  ),
        .op_i       ( op_i       ),
        .data_i     ( data_i     ),
        .mask_i     ( mask_i     ),
        .prd_i      ( prd_i[7:0] ),
        .data_o     ( data_o     ),
        .mask_o     ( mask_o     )
      );

      `ASSERT_INIT(AesWidthPRDSBox, WidthPRDSBox == 8)

    end else if (SBoxImpl == SBoxImplCanrightMaskedNoreuse) begin : gen_sbox_canright_masked_noreuse
      // Tie off unused inputs.
      logic unused_clk;
      logic unused_rst;
      assign unused_clk = clk_i;
      assign unused_rst = rst_ni;
      if (WidthPRDSBox > 18) begin : gen_unused_prd
        logic [WidthPRDSBox-1-18:0] unused_prd;
        assign unused_prd = prd_i[WidthPRDSBox-1:18];
      end

      aes_sbox_canright_masked_noreuse u_aes_sbox (
        .op_i   ( op_i        ),
        .data_i ( data_i      ),
        .mask_i ( mask_i      ),
        .prd_i  ( prd_i[17:0] ),
        .data_o ( data_o      ),
        .mask_o ( mask_o      )
      );

      `ASSERT_INIT(AesWidthPRDSBox, WidthPRDSBox == 18)

    end else begin : gen_sbox_canright_masked // SBoxImpl == SBoxImplCanrightMasked
      // Tie off unused inputs.
      logic  unused_clk;
      logic  unused_rst;
      assign unused_clk = clk_i;
      assign unused_rst = rst_ni;
      if (WidthPRDSBox > 8) begin : gen_unused_prd
        logic [WidthPRDSBox-1-8:0] unused_prd;
        assign unused_prd = prd_i[WidthPRDSBox-1:8];
      end

      aes_sbox_canright_masked u_aes_sbox (
        .op_i   ( op_i       ),
        .data_i ( data_i     ),
        .mask_i ( mask_i     ),
        .prd_i  ( prd_i[7:0] ),
        .data_o ( data_o     ),
        .mask_o ( mask_o     )
      );

      `ASSERT_INIT(AesWidthPRDSBox, WidthPRDSBox == 8)
    end
  end

  if (SBoxSingleCycle) begin : gen_req_singlecycle
    // Tie off unused inputs.
    logic unused_out_ack;
    assign unused_out_ack = out_ack_i;

    // Signal that we have valid output right away.
    assign out_req_o = en_i;
  end

endmodule
