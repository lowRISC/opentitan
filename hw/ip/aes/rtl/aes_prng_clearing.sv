// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES low-bandwidth pseudo-random number generator for register clearing
//
// This module uses an LFSR connected to a PRINCE S-Box and PRESENT permutation to generate
// pseudo-random data for the AES module for clearing registers. The LFSR can be reseeded
// using an external interface.

`include "prim_assert.sv"

module aes_prng_clearing import aes_pkg::*;
#(
  parameter int unsigned Width = 64, // At the moment we just support a width of 64.
  parameter clearing_lfsr_seed_t RndCnstLfsrSeed = RndCnstClearingLfsrSeedDefault,
  parameter clearing_lfsr_perm_t RndCnstLfsrPerm = RndCnstClearingLfsrPermDefault
) (
  input  logic        clk_i,
  input  logic        rst_ni,

  // Connections to AES internals, PRNG consumers
  input  logic             data_req_i,
  output logic             data_ack_o,
  output logic [Width-1:0] data_o,
  input  logic             reseed_req_i,
  output logic             reseed_ack_o,

  // Connections to outer world, LFSR re-seed
  output logic             entropy_req_o,
  input  logic             entropy_ack_i,
  input  logic [Width-1:0] entropy_i
);

  logic             seed_en;
  logic             lfsr_en;
  logic [Width-1:0] lfsr_state;

  // The data requests are fed from the LFSR, reseed requests have the highest priority.
  assign data_ack_o    = reseed_req_i ? 1'b0 : data_req_i;

  // Reseed requests are directly forwarded to the external interface.
  assign reseed_ack_o  = entropy_ack_i;
  assign entropy_req_o = reseed_req_i;

  // LFSR control
  assign lfsr_en = data_req_i & data_ack_o;
  assign seed_en = entropy_req_o & entropy_ack_i;

  // LFSR instance
  prim_lfsr #(
    .LfsrType    ( "GAL_XOR"       ),
    .LfsrDw      ( Width           ),
    .StateOutDw  ( Width           ),
    .DefaultSeed ( RndCnstLfsrSeed ),
    .StatePermEn ( 1'b1            ),
    .StatePerm   ( RndCnstLfsrPerm )
  ) u_lfsr (
    .clk_i     ( clk_i      ),
    .rst_ni    ( rst_ni     ),
    .seed_en_i ( seed_en    ),
    .seed_i    ( entropy_i  ),
    .lfsr_en_i ( lfsr_en    ),
    .entropy_i (         '0 ),
    .state_o   ( lfsr_state )
  );

  // "Scramble" the LFSR state to break linear shift patterns.
  assign data_o = prim_cipher_pkg::sbox4_64bit(lfsr_state, prim_cipher_pkg::PRINCE_SBOX4);

  // Width must be 64.
  `ASSERT_INIT(AesPrngWidth, Width == 64)

endmodule
