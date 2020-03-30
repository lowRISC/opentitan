// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES pseudo-random number generator
//
// This module uses an LFSR connected to a PRINCE S-Box to provide pseudo-random data to the AES
// module primarily for clearing registers. The LFSR can be reseeded using an external interface.

module aes_prng(
  input  logic        clk_i,
  input  logic        rst_ni,

  // Connections to AES internals, PRNG consumers
  input  logic        data_req_i,
  output logic        data_ack_o,
  output logic [63:0] data_o,
  input  logic        reseed_req_i,
  output logic        reseed_ack_o,

  // Connections to outer world, LFSR re-seed
  output logic        entropy_req_o,
  input  logic        entropy_ack_i,
  input  logic [63:0] entropy_i
);

  localparam int unsigned DATA_WIDTH = 64;

  // The S-Box of the PRINCE cipher is used to "scramble" the LFSR output.
  localparam logic[15:0][3:0] PRINCE_SBOX_FWD = {4'h4, 4'hD, 4'h5, 4'hE,
                                                 4'h0, 4'h8, 4'h7, 4'h6,
                                                 4'h1, 4'h9, 4'hC, 4'hA,
                                                 4'h2, 4'h3, 4'hF, 4'hB};

  // "Scramble" with PRINCE cipher S-Box.
  function automatic logic [63:0] aes_prng_scramble(logic [63:0] in);
    logic [63:0] out;
    // The PRINCE cipher S-Box operates on 4-bit nibbles.
    for (int i=0; i<16; i++) begin
      out[i*4 +: 4] = PRINCE_SBOX_FWD[in[i*4 +: 4]];
    end
    return out;
  endfunction

  logic [DATA_WIDTH-1:0] lfsr_state;
  logic                  lfsr_en;
  logic                  seed_en;

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
    .LfsrType    ( "GAL_XOR"  ),
    .LfsrDw      ( DATA_WIDTH ),
    .StateOutDw  ( DATA_WIDTH )
  ) aes_prng_lfsr (
    .clk_i     ( clk_i      ),
    .rst_ni    ( rst_ni     ),
    .seed_en_i ( seed_en    ),
    .seed_i    ( entropy_i  ),
    .lfsr_en_i ( lfsr_en    ),
    .entropy_i (         '0 ),
    .state_o   ( lfsr_state )
  );

  // "Scramble" the LFSR state.
  assign data_o = aes_prng_scramble(lfsr_state);

endmodule
