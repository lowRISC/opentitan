// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Reduced KMAC/SHA3 core including PRNG but without TL-UL interface. This module is suitable for
// SCA using e.g. PROLEAD.

`include "prim_assert.sv"

module kmac_reduced
  import kmac_pkg::*;
  import kmac_reg_pkg::*;
  import sha3_pkg::*;
#(
  // EnMasking: Enable masking security hardening inside keccak_round.
  parameter bit EnMasking = 1,
  localparam int NumShares = (EnMasking) ? 2 : 1, // derived parameter

  // For now, we use a fixed message length of 128 bits to mirror some of the initial FPGA
  // experiments.
  parameter int unsigned MsgLen = 128,
  parameter int unsigned EntropyWidth = 32,

  parameter lfsr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault,
  parameter lfsr_seed_t RndCnstLfsrSeed = RndCnstLfsrSeedDefault,
  parameter buffer_lfsr_seed_t RndCnstBufferLfsrSeed = RndCnstBufferLfsrSeedDefault,
  parameter msg_perm_t RndCnstMsgPerm = RndCnstMsgPermDefault
) (
  input logic clk_i,
  input logic rst_ni,

  // Inputs exercised by SCA tools.
  // Pre-masked message input. The message is provided in one shot to facilitate the interfacing.
  input  logic [MsgLen-1:0] msg_i [NumShares],
  input  logic              msg_valid_i,
  output logic              msg_ready_o,

  // SHA3 control and status
  input  logic                  start_i,           // 1 pulse after reseeding PRNG and injecting
                                                   // message
  input  logic                  process_i,         // 1 pulse after loading message into SHA3
  input  logic                  run_i,             // drive to 0
  input  prim_mubi_pkg::mubi4_t done_i,            // drive to MuBi4True after
                                                   // absorbed_o == MuBi4True
  output prim_mubi_pkg::mubi4_t absorbed_o,
  output logic                  squeezing_o,
  output logic                  block_processed_o,
  output sha3_st_e              sha3_fsm_o,

  // Entropy interface
  input  logic                    entropy_ready_i,       // drive to 1 once ready
  input  logic                    entropy_refresh_req_i, // one pulse at the beginning
  input  logic [EntropyWidth-1:0] entropy_i,
  output logic                    entropy_req_o,
  input  logic                    entropy_ack_i,

  // Inputs driven with constant values for evaluation but we want to avoid synthesis optimizing
  // them.
  // SHA3 configuration
  input sha3_mode_e                    mode_i,      // e.g. sha3_pkg::Sha3
  input keccak_strength_e              strength_i,  // e.g. sha3_pkg::L256
  input logic [NSRegisterSize*8-1:0]   ns_prefix_i, // Ignored for Sha3,
                                                    // 48'h4341_4D4B_2001 for CShake
  input logic [sha3_pkg::MsgStrbW-1:0] msg_strb_i,  // drive to all-1

  // Entropy configuration
  input logic          msg_mask_en_i,          // drive to 1
  input entropy_mode_e entropy_mode_i,         // drive to kmac_pkg::EntropyModeEdn
  input logic          entropy_fast_process_i, // drive to 0
  input logic          entropy_in_keyblock_i,  // drive to 1

  // Entropy reseed control
  input logic                       entropy_seed_update_i,  // drive to 0
  input logic [31:0]                entropy_seed_data_i,    // drive to 0
  input logic [TimerPrescalerW-1:0] wait_timer_prescaler_i, // drive to 0
  input logic [EdnWaitTimerW-1:0]   wait_timer_limit_i,     // drive to EdnWaitTimerW'1

  // Signals primarily kept to prevent them from being optimized away during synthesis.
  // State output
  output logic [StateW-1:0] state_o [NumShares],
  output logic              state_valid_o,

  // Entropy status signals
  output prim_mubi_pkg::mubi4_t entropy_configured_o,
  input  logic [HashCntW-1:0]   entropy_hash_threshold_i, // drive to max
  input  logic                  entropy_hash_clr_i,       // drive to 0
  output logic [HashCntW-1:0]   entropy_hash_cnt_o,

  // Life cycle interface
  input lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  // Error signaling
  output logic err_o,
  input  logic err_processed_i // drive 0
);

  ///////////////////////////////////
  // Message unpacking & injection //
  ///////////////////////////////////
  // Message packer FIFO
  logic [sha3_pkg::MsgWidth-1:0] msg [NumShares];
  logic [NumShares-1:0] msg_valid_shares;
  logic [NumShares-1:0] msg_ready_shares;
  logic msg_valid, msg_ready;

  prim_packer_fifo #(
    .InW(MsgLen),
    .OutW(sha3_pkg::MsgWidth),
    .ClearOnRead(1'b1)
  ) u_msg_unpacker_share0 (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(msg_valid_i),
    .wdata_i (msg_i[0]),
    .wready_o(msg_ready_shares[0]),
    .rvalid_o(msg_valid_shares[0]),
    .rdata_o (msg[0]),
    .rready_i(msg_ready),
    .depth_o ()
  );

  prim_packer_fifo #(
    .InW(MsgLen),
    .OutW(sha3_pkg::MsgWidth),
    .ClearOnRead(1'b1)
  ) u_msg_unpacker_share1 (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(msg_valid_i),
    .wdata_i (msg_i[1]),
    .wready_o(msg_ready_shares[1]),
    .rvalid_o(msg_valid_shares[1]),
    .rdata_o (msg[1]),
    .rready_i(msg_ready),
    .depth_o ()
  );

  // Reduce valid/ready signals driven by the packer FIFOs.
  assign msg_ready_o = &msg_ready_shares;
  assign msg_valid = &msg_valid_shares;

  //////////////////////////
  // Message (re-)masking //
  //////////////////////////
  logic msg_mask_en;
  logic [sha3_pkg::MsgWidth-1:0] msg_mask, msg_mask_permuted;
  logic [sha3_pkg::MsgWidth-1:0] msg_masked [NumShares];

  // Permute the PRNG output.
  always_comb begin
    msg_mask_permuted = '0;
    for (int unsigned i = 0 ; i < sha3_pkg::MsgWidth ; i++) begin
      // Loop through the MsgPerm constant and swap between the bits
      msg_mask_permuted[i] = msg_mask[RndCnstMsgPerm[i]];
    end
  end

  // Perform the actual (re-)masking
  for (genvar i = 0; i < NumShares; i++) begin: gen_msg_masking
    assign msg_masked[i] =
        msg[i] ^ ({sha3_pkg::MsgWidth{msg_mask_en_i}} & msg_mask_permuted);
  end

  assign msg_mask_en = msg_mask_en_i & msg_valid & msg_ready;

  // SHA3 entropy interface
  logic sha3_rand_valid, sha3_rand_early, sha3_rand_update, sha3_rand_consumed;
  logic [StateW/2-1:0] sha3_rand_data;
  logic sha3_rand_aux;

  // Life cycle signals
  localparam int unsigned NumLcSyncCopies = 2;
  lc_ctrl_pkg::lc_tx_t [NumLcSyncCopies-1:0] lc_escalate_en;

  // Synchronize life cycle input.
  prim_lc_sync #(
    .NumCopies (NumLcSyncCopies)
  ) u_prim_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_escalate_en_i),
    .lc_en_o(lc_escalate_en)
  );

  // Error signals
  sha3_pkg::err_t sha3_err, entropy_err;
  logic sha3_state_error, sha3_count_error, sha3_storage_rst_error;
  logic entropy_state_error, entropy_hash_counter_error;

  // Collect error signals.
  assign err_o = |{sha3_err, sha3_state_error, sha3_count_error, sha3_storage_rst_error,
                   entropy_err, entropy_state_error, entropy_hash_counter_error};

  /////////////////
  // SHA3 engine //
  /////////////////
  sha3 #(
    .EnMasking(EnMasking)
  ) u_sha3 (
    .clk_i,
    .rst_ni,

    // MSG_FIFO interface (or from KMAC)
    .msg_valid_i(msg_valid),
    .msg_data_i (msg_masked),
    .msg_strb_i (msg_strb_i),
    .msg_ready_o(msg_ready),

    // Entropy interface
    .rand_valid_i    (sha3_rand_valid),
    .rand_early_i    (sha3_rand_early),
    .rand_data_i     (sha3_rand_data),
    .rand_aux_i      (sha3_rand_aux),
    .rand_update_o   (sha3_rand_update),
    .rand_consumed_o (sha3_rand_consumed),

    // N, S: Used in cSHAKE mode
    .ns_data_i (ns_prefix_i),

    // Configurations
    .mode_i,
    .strength_i,

    // Control and status
    .start_i,           // Start receiving message.
    .process_i,         // Stop receiving message, start padding and afterwards processing.
    .run_i,             // Manually trigger processing after absorption.
    .done_i,            // Clear internal variables and move back into Idle state.
    .absorbed_o,        // Absorption process is done.
    .squeezing_o,       // Currently running manually triggered processing after absorption.
    .block_processed_o,
    .sha3_fsm_o,

    // State output
    .state_valid_o(state_valid_o),
    .state_o      (state_o),

    // REQ/ACK interface to avoid power spikes
    .run_req_o(),     // Not used
    .run_ack_i(1'b1), // The SHA3 core is always allowed to process.

    // LC escalation
    .lc_escalate_en_i(lc_escalate_en[0]),

    // Error signals
    .error_o                   (sha3_err),
    .sparse_fsm_error_o        (sha3_state_error),
    .count_error_o             (sha3_count_error),
    .keccak_storage_rst_error_o(sha3_storage_rst_error)
  );

  //////////
  // PRNG //
  //////////
  kmac_entropy #(
    .RndCnstLfsrPerm(RndCnstLfsrPerm),
    .RndCnstLfsrSeed(RndCnstLfsrSeed),
    .RndCnstBufferLfsrSeed(RndCnstBufferLfsrSeed)
  ) u_entropy (
    .clk_i,
    .rst_ni,

    // EDN interface
    .entropy_req_o (entropy_req_o),
    .entropy_ack_i (entropy_ack_i),
    .entropy_data_i(entropy_i),

    // SHA3 interface
    .rand_valid_o   (sha3_rand_valid),
    .rand_early_o   (sha3_rand_early),
    .rand_data_o    (sha3_rand_data),
    .rand_aux_o     (sha3_rand_aux),
    .rand_update_i  (sha3_rand_update),
    .rand_consumed_i(sha3_rand_consumed),

    // Message Masking
    .msg_mask_en_i(msg_mask_en),
    .msg_mask_o   (msg_mask),

    // Configuration
    .mode_i         (entropy_mode_i),
    .entropy_ready_i(entropy_ready_i),
    .fast_process_i (entropy_fast_process_i),
    .in_keyblock_i  (entropy_in_keyblock_i),

    // Reseed control
    .entropy_refresh_req_i (entropy_refresh_req_i),
    .seed_update_i         (entropy_seed_update_i),
    .seed_data_i           (entropy_seed_data_i),
    .wait_timer_prescaler_i(wait_timer_prescaler_i),
    .wait_timer_limit_i    (wait_timer_limit_i),

    // Status
    .hash_threshold_i(entropy_hash_threshold_i),
    .hash_cnt_clr_i  (entropy_hash_clr_i),
    .hash_cnt_o      (entropy_hash_cnt_o),

    .entropy_configured_o(entropy_configured_o),

    // LC escalation
    .lc_escalate_en_i(lc_escalate_en[1]),

    // Error signals
    .err_o             (entropy_err),
    .sparse_fsm_error_o(entropy_state_error),
    .count_error_o     (entropy_hash_counter_error),
    .err_processed_i   (err_processed_i)
  );

endmodule
