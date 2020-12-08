// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES SBox

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
  input  logic              [7:0] in_mask_i,
  input  logic              [7:0] out_mask_i,
  input  logic [WidthPRDSBox-1:0] prd_masking_i,
  output logic              [7:0] data_o
);

  import aes_pkg::*;
  localparam bit SBoxMasked = (SBoxImpl == SBoxImplCanrightMasked ||
                               SBoxImpl == SBoxImplCanrightMaskedNoreuse) ? 1'b1 : 1'b0;

  localparam bit SBoxSingleCycle = 1'b1;

  if (!SBoxMasked) begin : gen_sbox_unmasked
    // Tie off unused inputs.
    logic                    unused_clk;
    logic                    unused_rst;
    logic             [15:0] unused_masks;
    logic [WidthPRDSBox-1:0] unused_prd;
    assign unused_clk   = clk_i;
    assign unused_rst   = rst_ni;
    assign unused_masks = {in_mask_i, out_mask_i};
    assign unused_prd   = prd_masking_i;

    if (SBoxImpl == SBoxImplCanright) begin : gen_sbox_canright
      aes_sbox_canright u_aes_sbox (
        .op_i,
        .data_i,
        .data_o
      );
    end else begin : gen_sbox_lut // SBoxImpl == SBoxImplLut
      aes_sbox_lut u_aes_sbox (
        .op_i,
        .data_i,
        .data_o
      );
    end
  end else begin : gen_sbox_masked

    if (SBoxImpl == SBoxImplCanrightMaskedNoreuse) begin : gen_sbox_canright_masked_noreuse
      // Tie off unused inputs.
      logic unused_clk;
      logic unused_rst;
      assign unused_clk = clk_i;
      assign unused_rst = rst_ni;

      aes_sbox_canright_masked_noreuse u_aes_sbox (
        .op_i,
        .data_i,
        .in_mask_i,
        .out_mask_i,
        .prd_masking_i,
        .data_o
      );
    end else begin : gen_sbox_canright_masked // SBoxImpl == SBoxImplCanrightMasked
      // Tie off unused inputs.
      logic                    unused_clk;
      logic                    unused_rst;
      logic [WidthPRDSBox-1:0] unused_prd;
      assign unused_clk = clk_i;
      assign unused_rst = rst_ni;
      assign unused_prd = prd_masking_i;

      aes_sbox_canright_masked u_aes_sbox (
        .op_i,
        .data_i,
        .in_mask_i,
        .out_mask_i,
        .data_o
      );
    end
  end

  if (SBoxSingleCycle) begin : gen_req_singlecycle
    // Tie off unused inputs.
    logic unused_out_ack;
    assign unused_out_ack = out_ack_i;

    // Signal that we have valid output right away.
    assign out_req_o = en_i;
  end else begin : gen_req_multicycle

    // All currently implemented S-Boxes allow for single-cycle operation. Future S-Box
    // implementations may require multiple clock cycles. The counter below is for mimicking such
    // implementations. It's for testing purposes only.

    // Counter register
    logic [2:0] count_d, count_q;
    assign count_d = (out_req_o && out_ack_i) ? '0                :
                     out_req_o                ? count_q           :
                     en_i                     ? count_q + 3'b001 : count_q;
    always_ff @(posedge clk_i or negedge rst_ni) begin : reg_count
      if (!rst_ni) begin
        count_q <= '0;
      end else begin
        count_q <= count_d;
      end
    end
    assign out_req_o = en_i & count_q == 3'b111;
  end

endmodule
