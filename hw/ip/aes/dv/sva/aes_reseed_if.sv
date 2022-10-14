// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

interface aes_reseed_if
  import aes_pkg::*;
  import aes_reg_pkg::*;
#(
  parameter int unsigned Width        = 64, // At the moment we just support a width of 64.
  parameter int unsigned EntropyWidth = edn_pkg::ENDPOINT_BUS_WIDTH,
  parameter bit          SecMasking   = `EN_MASKING
) (
  input logic                                      clk_i,
  input logic                                      rst_ni,
  input                                            lc_ctrl_pkg::lc_tx_t local_esc,
  input logic                                      entropy_clearing_req,
  input logic                                      entropy_clearing_ack,
  input logic                                      entropy_masking_req,
  input logic                                      entropy_masking_ack,
  input                                            prs_rate_e prng_reseed_rate,
  input logic                                      entropy_req_o,
  input logic                                      entropy_ack_i,
  input logic                                      seed_en,
  input logic [EntropyWidth-1:0]                   entropy_i,
  input logic [EntropyWidth-1:0]                   buffer_q,
  input logic [Width-1:0]                          lfsr_q,
  input logic                                      ctrl_phase_i,
  input logic                                      ctrl_we_q,
  input logic                                      block_ctr_decr,
  input logic                                      block_ctr_expr,
  input logic [3:0][3:0][7:0]                      add_round_key_out[SecMasking ? 2 : 1],
  input logic [NumSlicesCtr-1:0][SliceSizeCtr-1:0] iv_q,
  input logic [NumSlicesCtr-1:0][SliceSizeCtr-1:0] iv_d,
  input logic [NumRegsData-1:0][31:0]              data_in_prev_q,
  input logic [NumRegsData-1:0][31:0]              data_out_q,
  input logic [NumRegsData-1:0][31:0]              data_out_d
  );

  logic [3:0][3:0][7:0]                            round_key;
  logic [3:0][3:0][7:0]                            data_out;

  logic [Width-1:0] seed;
  assign seed = {buffer_q, entropy_i};

  // make sure clearing PRNG LSFR input always matches the EDN input
  `ASSERT(ClearingPrngInputMatchesEdnInput_A, seed_en |-> ##1 seed == lfsr_q);

  // make sure masking PRNG reseeded at the specified rate
  // check the reseed rate for per_1 reseed rate
  `ASSERT(MaskingPrngReseedRatePer1_A, (SecMasking && prng_reseed_rate == PER_1 &&
          block_ctr_decr) |-> ##[1:$] entropy_masking_req);
  // check the reseed rate for per_64 or per_8k reseed rate
  `ASSERT(MaskingPrngReseedRate_A, ( SecMasking && (prng_reseed_rate == PER_64 |
          prng_reseed_rate == PER_8K) && block_ctr_expr) |-> ##[1:$] entropy_masking_req);
  // check the reseed happens after the block counter resets (when control register is updated)
  `ASSERT(MaskingPrngReseedCorrectAfter_A, (SecMasking && ctrl_we_q && !ctrl_phase_i) |->
          ##[1:$] entropy_masking_req);

  // local esc checks #15433
  assign round_key = SecMasking ?
         (add_round_key_out[1] ^ add_round_key_out[0]) : add_round_key_out[0];

  `ASSERT(DataOutRoundKey_A, !((local_esc == lc_ctrl_pkg::On) &&
                               (aes_transpose(round_key) == data_out_d )));
  `ASSERT(DataOutRoundKey_B, !((local_esc == lc_ctrl_pkg::On) &&
                              ((aes_transpose(round_key) == data_out_d )^iv_q)));
  `ASSERT(DataOutRoundKey_C, !((local_esc == lc_ctrl_pkg::On) &&
                              ((aes_transpose(round_key) == data_out_d )^data_in_prev_q)));
  `ASSERT(IvRoundKey_A,      !((local_esc == lc_ctrl_pkg::On) &&
                              ((aes_transpose(round_key) == iv_d ))));
  `ASSERT(IvRoundKey_B,      !((local_esc == lc_ctrl_pkg::On) &&
                              ((aes_transpose(round_key) == iv_d )^iv_q)));
  `ASSERT(IvRoundKey_C,      !((local_esc == lc_ctrl_pkg::On) &&
                              ((aes_transpose(round_key) == iv_d )^data_in_prev_q)));
endinterface // aes_reseed_if
