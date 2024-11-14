// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Wrapper for AES GHASH block suitable for pre-silicon SCA using e.g. Alma and PROLEAD.

module aes_ghash_wrap import aes_pkg::*;
(
  input  logic                 clk_i,
  input  logic                 rst_ni,

  // Input handshake signals
  input  logic                 in_valid_i,
  output logic                 in_ready_o,

  // Output handshake signals
  output logic                 out_valid_o,
  input  logic                 out_ready_i,

  // Control signals
  input  aes_op_e              op_i,
  input  gcm_phase_e           gcm_phase_i,
  input  logic [4:0]           num_valid_bytes_i,
  input  logic                 load_hash_subkey_i,
  input  logic                 clear_i,
  output logic                 first_block_o,
  input  logic                 alert_fatal_i,
  output logic                 alert_o,

  // Secrets
  input  logic [3:0][3:0][7:0] hash_subkey_i [2], // Needs to be muxed to cipher_state_done.
  input  logic [3:0][3:0][7:0] s_i [2],           // Needs to be muxed to cipher_state_done.

  // Randomness
  input  logic [3:0][3:0][7:0] prd_i [2],         // Needs to be muxed to cipher_state_done.

  // I/O data signals
  input  logic         [127:0] data_in_prev_i,    // Ciphertext for decryption or AAD
  input  logic     [3:0][31:0] data_out_i,        // Ciphertext for encryption
  output logic     [3:0][31:0] ghash_state_done_o,

  // Cycle counter for debugging.
  output logic           [7:0] cyc_ctr_o
);

  // Signals needing conversion
  sp2v_e in_valid;
  sp2v_e in_ready;
  sp2v_e out_valid;
  sp2v_e out_ready;
  sp2v_e load_hash_subkey;

  logic [3:0][3:0][7:0] cipher_state_done [2];
  logic [3:0][3:0][7:0] cipher_state_done_buf [2];

  // Sparse control signals
  assign in_valid         = in_valid_i         ? SP2V_HIGH : SP2V_LOW;
  assign out_ready        = out_ready_i        ? SP2V_HIGH : SP2V_LOW;
  assign load_hash_subkey = load_hash_subkey_i ? SP2V_HIGH : SP2V_LOW;

  assign in_ready_o  = in_ready  == SP2V_HIGH ? 1'b1 : 1'b0;
  assign out_valid_o = out_valid == SP2V_HIGH ? 1'b1 : 1'b0;

  // MUX the secrets and the pseudo-random data to the cipher_state_done input of the DUT.
  assign cipher_state_done = in_valid_i &&  clear_i            ? prd_i         :
                             in_valid_i &&  load_hash_subkey_i ? hash_subkey_i :
                             in_valid_i && !load_hash_subkey_i ? s_i           : prd_i;

  // These primitives are used to place a size-only constraint on the
  // buffers to act as a synthesis optimization barrier.
  prim_buf #(
    .Width ( 128 )
  ) u_prim_buf_0 (
    .in_i  ( cipher_state_done[0]     ),
    .out_o ( cipher_state_done_buf[0] )
  );
  prim_buf #(
    .Width ( 128 )
  ) u_prim_buf_1 (
    .in_i  ( cipher_state_done[1]     ),
    .out_o ( cipher_state_done_buf[1] )
  );

  // The actual GHASH module.
  aes_ghash #(
    .SecMasking   ( 1 ),
    .GFMultCycles ( 4 ) // We use a small value greater than 1 to speed up the verification but
                        // still get the pipelined multipler design.
  ) u_aes_ghash (
    .clk_i               ( clk_i                 ),
    .rst_ni              ( rst_ni                ),

    .in_valid_i          ( in_valid              ),
    .in_ready_o          ( in_ready              ),

    .out_valid_o         ( out_valid             ),
    .out_ready_i         ( out_ready             ),

    .op_i                ( op_i                  ),
    .gcm_phase_i         ( gcm_phase_i           ),
    .num_valid_bytes_i   ( num_valid_bytes_i     ),
    .load_hash_subkey_i  ( load_hash_subkey      ),
    .clear_i             ( clear_i               ),
    .first_block_o       ( first_block_o         ),
    .alert_fatal_i       ( alert_fatal_i         ),
    .alert_o             ( alert_o               ),

    .data_in_prev_i      ( data_in_prev_i        ),
    .data_out_i          ( data_out_i            ),
    .cipher_state_done_i ( cipher_state_done_buf ),
    .ghash_state_done_o  ( ghash_state_done_o    )
  );

  // Cycle counter for debugging.
  logic [7:0] cyc_ctr_d, cyc_ctr_q;
  assign cyc_ctr_d = cyc_ctr_q + 8'd1;
  always_ff @(posedge clk_i or negedge rst_ni) begin : cyc_ctr_reg
    if (!rst_ni) begin
      cyc_ctr_q <= '0;
    end else begin
      cyc_ctr_q <= cyc_ctr_d;
    end
  end
  assign cyc_ctr_o = cyc_ctr_q;

endmodule
