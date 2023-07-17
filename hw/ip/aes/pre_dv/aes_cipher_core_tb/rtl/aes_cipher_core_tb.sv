// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES cipher core testbench
//
// This simple testbench is mainly useful to perform some basic verification of, e.g., a
// synthesized version of the AES cipher core and/or to get an understanding of how to
// interface the core, e.g., for verifying security properties.
//
// The testbench instantiates the AES cipher core only. It performs mainly three things:
// 1. The internal masking PRNG is reseeded.
// 2. A couple of random plaintexts are encrypted with different key lenghts and random keys.
// 3. The ciphertexts produced during Step 2 are again decrypted and then compared against the
//    original plaintext values.
// While doing the encryptions and decryptions in Step 2 and Step 3, the masking PRNG is reseeded
// once per every block.

module aes_cipher_core_tb #(
) (
  input  logic clk_i,
  input  logic rst_ni,

  output logic test_done_o,
  output logic test_passed_o
);

  import aes_pkg::*;

  localparam bit          SecMasking   = 1;
  localparam sbox_impl_e  SecSBoxImpl  = SecMasking ? SBoxImplDom : SBoxImplCanright;
  localparam int          NumShares    = SecMasking ?           2 :                1;
  localparam int unsigned EntropyWidth = edn_pkg::ENDPOINT_BUS_WIDTH;

  // DUT signals
  sp2v_e                       in_ready, in_valid, out_valid;
  ciph_op_e                    op;
  key_len_e                    key_len_d, key_len_q;
  sp2v_e                       crypt, dec_key_gen;
  logic                        prng_reseed;
  logic [WidthPRDClearing-1:0] prd_clearing [NumShares];
  logic        [3:0][3:0][7:0] state_mask;
  logic        [3:0][3:0][7:0] state_init [NumShares];
  logic        [3:0][3:0][7:0] state_done [NumShares];
  logic            [7:0][31:0] key_init [NumShares];
  logic                        entropy_masking_req;
  logic     [EntropyWidth-1:0] entropy_masking;
  logic                        alert;

  // Instantiate DUT
  aes_cipher_core #(
    .SecMasking  ( SecMasking  ),
    .SecSBoxImpl ( SecSBoxImpl )
  ) u_aes_cipher_core (
    .clk_i            ( clk_i               ),
    .rst_ni           ( rst_ni              ),

    .in_valid_i       ( in_valid            ),
    .in_ready_o       ( in_ready            ),

    .out_valid_o      ( out_valid           ),
    .out_ready_i      ( SP2V_HIGH           ), // We're always ready.

    .cfg_valid_i      ( 1'b1                ), // Used for gating assertions only.
    .op_i             ( op                  ),
    .key_len_i        ( key_len_q           ),
    .crypt_i          ( crypt               ),
    .crypt_o          (                     ), // Ignored.
    .dec_key_gen_i    ( dec_key_gen         ),
    .dec_key_gen_o    (                     ), // Ignored.
    .prng_reseed_i    ( prng_reseed         ),
    .prng_reseed_o    (                     ), // Ignored.
    .key_clear_i      ( 1'b0                ), // Ignored.
    .key_clear_o      (                     ), // Ignored.
    .data_out_clear_i ( 1'b0                ), // Ignored.
    .data_out_clear_o (                     ), // Ignored.
    .alert_fatal_i    ( 1'b0                ), // Ignored.
    .alert_o          ( alert               ), // Ignored.

    .prd_clearing_i   ( prd_clearing        ),

    .force_masks_i    ( 1'b0                ), // Ignored.
    .data_in_mask_o   ( state_mask          ),
    .entropy_req_o    ( entropy_masking_req ),
    .entropy_ack_i    ( 1'b1                ), // This TB has always entropy available.
    .entropy_i        ( entropy_masking     ),

    .state_init_i     ( state_init          ),
    .key_init_i       ( key_init            ),
    .state_o          ( state_done          )
  );

  // TB signals.
  localparam int CipherCoreTbStateWidth = 3;
  typedef enum logic [CipherCoreTbStateWidth-1:0] {
    IDLE,
    INIT_RESEED,
    ECB_ENCRYPT,
    DEC_KEY_GEN,
    ECB_DECRYPT,
    FINISH
  } aes_cipher_core_tb_e;
  aes_cipher_core_tb_e  aes_cipher_core_tb_state_d, aes_cipher_core_tb_state_q;
  logic           [7:0] block_count_d, block_count_q;
  logic                 block_count_increment, block_count_clear;
  logic                 data_in_buf_we, data_out_buf_we, check, mismatch, test_done;
  logic [3:0][3:0][7:0] data_in_rand, data_in;
  logic [3:0][3:0][7:0] data_out;
  logic [3:0][3:0][7:0] data_in_buf[256];
  logic [3:0][3:0][7:0] data_out_buf[256];

  // Count the number of encrypted/decrypted blocks. We're doing 8 blocks with each
  // key length.
  assign block_count_d = block_count_clear     ? '0                 :
                         block_count_increment ? block_count_q + 8'h1 : block_count_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_count
    if (!rst_ni) begin
      block_count_q <= '0;
    end else begin
      block_count_q <= block_count_d;
    end
  end

  // Randomness generation.
  // Update once per block.
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_prd_clearing
    if (!rst_ni) begin
      prd_clearing <= '{default: '0};
    end else if (out_valid == SP2V_HIGH) begin
      prd_clearing <= '{default: {$urandom, $urandom}};
    end
  end

  // Update whenever requested.
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_entropy_masking
    if (!rst_ni) begin
      entropy_masking <= '0;
    end else if (entropy_masking_req) begin
      entropy_masking <= $urandom;
    end
  end

  // Input generation.
  // We use a random key. Independent of the key length, drive all key bits.
  assign key_init = '{default: {8{$urandom}}};
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_key_len
    if (!rst_ni) begin
      key_len_q <= AES_128;
    end else begin
      key_len_q <= key_len_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_data_in
    if (!rst_ni) begin
      data_in_rand <= '0;
    end else if (block_count_increment) begin
      data_in_rand <= {4{$urandom}};
    end
  end

  // For encryption we use the random data input. For decryption, we use the previous outputs.
  assign data_in =
      (aes_cipher_core_tb_state_q == ECB_DECRYPT) ? data_out_buf[block_count_q] : data_in_rand;

  // Generate the initial state.
  if (!SecMasking) begin : gen_state_init_no_masking
    // Only Share 0 is used.
    assign state_init[0] = data_in;

    // Tie-off unused signals.
    logic unused_bits;
    assign unused_bits = ^state_mask;
  end else begin : gen_state_init_masking
    // Mask the input data with the mask provided by the internal masking PRNG.
    assign state_init[0] = data_in ^ state_mask;
    assign state_init[1] = state_mask;
  end

  always_comb begin : aes_cipher_core_tb_fsm
    // DUT
    in_valid    = SP2V_LOW;
    op          = CIPH_FWD;
    crypt       = SP2V_HIGH;
    dec_key_gen = SP2V_LOW;
    prng_reseed = 1'b0;

    // TB
    aes_cipher_core_tb_state_d = aes_cipher_core_tb_state_q;
    block_count_increment      = 1'b0;
    block_count_clear          = 1'b0;
    key_len_d                  = key_len_q;
    data_in_buf_we             = 1'b0;
    data_out_buf_we            = 1'b0;
    check                      = 1'b0;
    test_done                  = 1'b0;

    unique case (aes_cipher_core_tb_state_q)

      IDLE: begin
        // Just wait for the ciphre core to become ready.
        if (in_ready == SP2V_HIGH) begin
          aes_cipher_core_tb_state_d = SecMasking ? INIT_RESEED : ECB_ENCRYPT;
        end
      end

      INIT_RESEED: begin
        // Perform an initial reseed of the internal masking PRNG to put it into a random state.
        in_valid    = SP2V_HIGH;
        crypt       = SP2V_LOW;
        prng_reseed = 1'b1;
        if (out_valid == SP2V_HIGH) begin
          aes_cipher_core_tb_state_d = ECB_ENCRYPT;
        end
      end

      ECB_ENCRYPT: begin
        // Perform encryption in parallel with a reseed of the internal masking PRNG.
        in_valid    = SP2V_HIGH;
        prng_reseed = 1'b1;
        if (out_valid == SP2V_HIGH) begin
          block_count_increment = 1'b1;
          data_in_buf_we  = 1'b1;
          data_out_buf_we = 1'b1;
          // Increase the key length after every 8 blocks.
          key_len_d = (block_count_q == 8'd7)  ? AES_192 :
                      (block_count_q == 8'd15) ? AES_256 : key_len_q;
          // After 24 blocks, we're starting over with decryption.
          if (block_count_q == 8'd23) begin
            block_count_clear          = 1'b1;
            key_len_d                  = AES_128;
            aes_cipher_core_tb_state_d = DEC_KEY_GEN;
          end
        end
      end

      DEC_KEY_GEN: begin
        // Perform encryption in parallel with a reseed of the internal masking PRNG.
        in_valid    = SP2V_HIGH;
        dec_key_gen = SP2V_HIGH;
        prng_reseed = 1'b1;
        if (out_valid == SP2V_HIGH) begin
          aes_cipher_core_tb_state_d = ECB_DECRYPT;
        end
      end

      ECB_DECRYPT: begin
        // Perform decryption in parallel with a reseed of the internal masking PRNG.
        in_valid    = SP2V_HIGH;
        op          = CIPH_INV;
        prng_reseed = 1'b1;
        if (out_valid == SP2V_HIGH) begin
          block_count_increment = 1'b1;
          check                 = 1'b1;
          // After every 8 blocks, we need to regenerate the next decryption key.
          if (block_count_q == 8'd7) begin
            key_len_d                  = AES_192;
            aes_cipher_core_tb_state_d = DEC_KEY_GEN;
          end else if (block_count_q == 8'd15) begin
            key_len_d                  = AES_256;
            aes_cipher_core_tb_state_d = DEC_KEY_GEN;
          end else if (block_count_q == 8'd23) begin
            aes_cipher_core_tb_state_d = FINISH;
          end
        end
      end

      FINISH: begin
        // Just signal end of simulation.
        test_done = 1'b1;
      end

      default: begin
        aes_cipher_core_tb_state_d = FINISH;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_fsm
    if (!rst_ni) begin
      aes_cipher_core_tb_state_q <= IDLE;
    end else begin
      aes_cipher_core_tb_state_q <= aes_cipher_core_tb_state_d;
    end
  end

  // Unmask the output.
  if (!SecMasking) begin : gen_data_out_no_masking
    assign data_out = (out_valid == SP2V_HIGH) ? state_done[0] : '0;
  end else begin : gen_data_out_masking
    assign data_out = (out_valid == SP2V_HIGH) ? state_done[1] ^ state_done[0] : '0;
  end

  // Buffering of encryption inputs and outputs for later decryption and comparison.
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_data_in_buf
    if (!rst_ni) begin
      data_in_buf <= '{default: '0};
    end else if (data_in_buf_we) begin
      data_in_buf[block_count_q] <= data_in;
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_data_out_buf
    if (!rst_ni) begin
      data_out_buf <= '{default: '0};
    end else if (data_out_buf_we) begin
      data_out_buf[block_count_q] <= data_out;
    end
  end

  // Check decryption results and signal potential mismatches.
  assign mismatch = check ? (data_out != data_in_buf[block_count_q]) : 1'b0;

  // Check responses, signal end of simulation
  always_ff @(posedge clk_i or negedge rst_ni) begin : tb_ctrl
    test_done_o   <= 1'b0;
    test_passed_o <= 1'b0;

    if (rst_ni && (aes_cipher_core_tb_state_q != IDLE)) begin
      if (alert) begin
        $display("\nERROR: Fatal alert condition detected.");
        test_done_o   <= 1'b1;
      end else if (mismatch) begin
        $display("\nERROR: AES output does not match expected value.");
        test_done_o   <= 1'b1;
      end else if (test_done) begin
        $display("\nSUCCESS: All AES ciphertexts correctly decrypted.");
        test_passed_o <= 1'b1;
        test_done_o   <= 1'b1;
      end
    end

    if (block_count_q == 8'hFF) begin
      $display("\nERROR: Simulation timed out.");
      test_done_o <= 1'b1;
    end
  end

endmodule
