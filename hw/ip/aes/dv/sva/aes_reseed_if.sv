// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface for verifying general PRNG reseed activity of AES. This interface is useful for
// verifying the reseeding of the clearing PRNG (always enabled), and correct behavior of
// the masking PRNG reseed req/ack signals, e.g., in case masking is disabled at compile time.

`include "prim_assert.sv"

interface aes_reseed_if
  import aes_pkg::*;
  import aes_reg_pkg::*;
#(
  parameter int unsigned Width        = 64, // At the moment we just support a width of 64.
  parameter int unsigned EntropyWidth = edn_pkg::ENDPOINT_BUS_WIDTH
) (
  input logic clk_i,
  input logic rst_ni,

  // Clearing PRNG related signals
  input logic                    entropy_clearing_req,
  input logic                    entropy_clearing_ack,
  input logic [EntropyWidth-1:0] entropy_i,
  input logic [EntropyWidth-1:0] buffer_q,
  input logic [Width-1:0]        lfsr_q,
  input logic                    seed_en,

  // Control signals
  input logic key_touch_forces_reseed,
  input logic key_init_new_pulse,
  input logic alert_fatal,

  // Masking PRNG related signals. They are checked by aes_reseed_vseq.sv independent whether
  // masking is enabled or not.
  input logic entropy_masking_req,
  input logic entropy_masking_ack
);

  logic [Width-1:0] seed;
  assign seed = {buffer_q, entropy_i};

  // Make sure the LFSR of the clearing PRNG is set to the correct value.
  `ASSERT(ClearingPrngStateMatchesEdnInput_A, seed_en |-> ##1 seed == lfsr_q)

  // Make sure the PRNGs get reseeded as expected based on the KEY_TOUCH_FORCES_RESEED control bit.
  `ASSERT(KeyTouchForcesReseed_A, key_touch_forces_reseed && key_init_new_pulse |->
    ##[1:20] entropy_clearing_req && (`EN_MASKING == entropy_masking_req) || alert_fatal)

endinterface // aes_reseed_if
