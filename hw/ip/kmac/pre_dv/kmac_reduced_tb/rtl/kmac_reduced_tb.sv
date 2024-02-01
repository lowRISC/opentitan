// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC reduced testbench

module kmac_reduced_tb #(
) (
  input  logic clk_i,
  input  logic rst_ni,

  output logic test_done_o,
  output logic test_passed_o
);

  import kmac_pkg::*;
  import kmac_reg_pkg::*;
  import sha3_pkg::*;

  // EnMasking: Enable masking security hardening inside keccak_round.
  parameter bit EnMasking = 1;
  localparam int NumShares = (EnMasking) ? 2 : 1;

  // For now, we use a fixed message length of 128 bits to mirror some of the initial FPGA
  // experiments.
  parameter int unsigned MsgWidthChunks = 2;
  parameter int unsigned MsgLen = MsgWidth * MsgWidthChunks;
  parameter int unsigned EntropyWidth = 32;

  // For now, we do SHA3-256.
  parameter int unsigned DigestLen = 256;
  parameter int unsigned DigestLenBytes = 256/8;

  // DUT signals
  logic [MsgLen-1:0] msg [NumShares];
  logic msg_valid, msg_ready;
  logic [StateW-1:0] state [NumShares];
  logic state_valid;
  logic sha3_start, sha3_process;
  prim_mubi_pkg::mubi4_t done, absorbed;
  sha3_st_e sha3_fsm;
  logic entropy_ready;
  logic entropy_refresh_req;
  logic [EntropyWidth-1:0] entropy;
  logic entropy_req;
  logic error;

  // Instantiate DUT
  kmac_reduced #(
    .EnMasking(EnMasking),
    .MsgLen(MsgLen),
    .EntropyWidth(EntropyWidth),
  ) u_kmac_reduced (
    .clk_i,
    .rst_ni,

    // Inputs exercised by SCA tools.
    // Pre-masked message input. The message is provided in one shot to facilitate the interfacing.
    .msg_i(msg),
    .msg_valid_i(msg_valid),
    .msg_ready_o(msg_ready),

    // SHA3 control and status
    .start_i(sha3_start),      // 1 pulse after reseeding PRNG and injecting
                               // messsage
    .process_i(sha3_process),  // 1 pulse after loading message into SHA3
    .run_i(1'b0),              // drive to 0
    .done_i(done),             // drive to MuBi4True after
                               // absorbed_o == MuBi4True
    .absorbed_o(absorbed),
    .squeezing_o(),
    .block_processed_o(),
    .sha3_fsm_o(sha3_fsm),

    // Entropy interface
    .entropy_ready_i(entropy_ready),
    .entropy_refresh_req_i(entropy_refresh_req),
    .entropy_i(entropy),
    .entropy_req_o(entropy_req),
    .entropy_ack_i(1'b1),

    // Inputs driven with constant values for evaluation but we want to avoid synthesis optimizing
    // them.
    // SHA3 configuration
    .mode_i(Sha3),                     // sha3_pkg::Sha3
    .strength_i(L256),                 // sha3_pkg::L256
    .ns_prefix_i(352'h4341_4D4B_2001), // Ignored for Sha3,
                                       // 48'h4341_4D4B_2001 ("KMAC") for CShake
    .msg_strb_i({MsgStrbW{1'b1}}),     // drive to all-1

    // Entropy configuration
    .msg_mask_en_i(1'b1),            // drive to 1
    .entropy_mode_i(EntropyModeEdn), // drive to kmac_pkg::EntropyModeEdn
    .entropy_fast_process_i(1'b0),   // drive to 0
    .entropy_in_keyblock_i(1'b1),    // drive to 1

    // Entropy reseed control
    .entropy_seed_update_i('0),                 // drive to 0
    .entropy_seed_data_i('0),                   // drive to 0
    .wait_timer_prescaler_i('0),                // drive to 0
    .wait_timer_limit_i({EdnWaitTimerW{1'b1}}), // drive to EdnWaitTimerW'1

    // Signals primarily kept to prevent them from being optimized away during synthesis.
    // State output
    .state_o(state),
    .state_valid_o(state_valid),

    // Entropy status signals
    .entropy_configured_o(),
    .entropy_hash_threshold_i({HashCntW{1'b1}}), // drive to max
    .entropy_hash_clr_i(1'b0),                   // drive to 0
    .entropy_hash_cnt_o(),

    // Life cycle interface
    .lc_escalate_en_i(lc_ctrl_pkg::Off),

    // Error signaling
    .err_o(error),
    .err_processed_i(1'b0)  // drive 0
  );

  // TB signals.
  localparam int KmacReducedTbStateWidth = 3;
  typedef enum logic [KmacReducedTbStateWidth-1:0] {
    IDLE,
    INIT_RESEED,
    START_TRIGGER,
    MSG_VALID,
    MSG_LOAD,
    PROCESSING,
    DONE,
    FINISH
  } kmac_reduced_tb_e;
  kmac_reduced_tb_e kmac_reduced_tb_state_d, kmac_reduced_tb_state_q;
  logic             entropy_req_d, entropy_req_q, entropy_req_fell;
  logic       [7:0] reseed_count_d, reseed_count_q;
  logic             reseed_count_increment;
  logic             msg_handshake, test_done;

  // Counter to control the simulation.
  localparam int unsigned CountWidth = 10;
  logic [CountWidth-1:0] count_d, count_q;
  assign count_d = count_q + 10'd1;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_count
    if (!rst_ni) begin
      count_q <= '0;
    end else begin
      count_q <= count_d;
    end
  end

  // Count the number of encrypted/decrypted blocks. We're doing 8 blocks with each
  // key length.
  assign reseed_count_d = reseed_count_increment ? reseed_count_q + 8'h1 : reseed_count_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_reseed_count
    if (!rst_ni) begin
      reseed_count_q <= '0;
    end else begin
      reseed_count_q <= reseed_count_d;
    end
  end

  assign msg_handshake = msg_valid & msg_ready;

  // Randomness generation.
  // Track falling edges of entropy_req. The end of the reseed operation is signaled with
  // entropy_req going low.
  assign entropy_req_d = entropy_req;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_entropy_req
    if (!rst_ni) begin
      entropy_req_q <= '0;
    end else begin
      entropy_req_q <= entropy_req_d;
    end
  end
  assign entropy_req_fell = entropy_req_q & ~entropy_req;

  // Update whenever requested.
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_entropy
    if (!rst_ni) begin
      entropy <= $urandom;
    end else if (entropy_req) begin
      entropy <= $urandom;
    end
  end

  // Input generation.
  // We use random messages.
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_msg
    if (!rst_ni) begin
      msg[0] <= {2*MsgWidthChunks{$urandom}};
    end else if (msg_handshake) begin
      msg[0] <= {2*MsgWidthChunks{$urandom}};
    end
  end
  // The second share is fixed to a deterministic value. This is clearly not how this should be
  // done in practice but using one deterministic share eases visual inspection of the message
  // remasking performed internally to the module.
  for (genvar i = 0; i < MsgLen / 32; i++) begin: gen_msg_share1
    assign msg[1][i*32 +: 32] = {8{i[3:0]}};
  end

  always_comb begin : kmac_reduced_tb_fsm
    // DUT
    msg_valid = 1'b0;
    sha3_start = 1'b0;
    sha3_process = 1'b0;
    done = prim_mubi_pkg::MuBi4False;
    entropy_ready = 1'b0;
    entropy_refresh_req = 1'b0;

    // TB
    kmac_reduced_tb_state_d = kmac_reduced_tb_state_q;
    reseed_count_increment = 1'b0;
    test_done = 1'b0;

    unique case (kmac_reduced_tb_state_q)

      IDLE: begin
        // Just move to INIT_RESEED
        if (count_q > 10'd2) begin
          entropy_ready = 1'b1;
          kmac_reduced_tb_state_d = INIT_RESEED;
        end
      end

      INIT_RESEED: begin
        // Perform an initial reseed of the PRNG to put it into a random state.
        // We do one reseed operation to reseed the single Bivium primitive.
        entropy_refresh_req = 1'b1;
        reseed_count_increment = entropy_req_fell;
        if (reseed_count_q == 8'd1) begin
          entropy_refresh_req = 1'b0;
          kmac_reduced_tb_state_d = START_TRIGGER;
        end
      end

      START_TRIGGER: begin
        // Simply send the Start pulse.
        sha3_start = 1'b1;
        kmac_reduced_tb_state_d = MSG_VALID;
      end

      MSG_VALID: begin
        // Write the full message into the unpacker FIFOs in one shot.
        msg_valid = 1'b1;
        kmac_reduced_tb_state_d = MSG_LOAD;
      end

      MSG_LOAD: begin
        // Wait until the unpacker FIFOs become ready again. This means the entire message has
        // been loaded into the SHA3 core and the Process pulse can be sent.
        if (msg_ready) begin
          sha3_process = 1'b1;
          kmac_reduced_tb_state_d = PROCESSING;
        end
      end

      PROCESSING: begin
        // Wait for the actual absorption process to finish. Note block_processed_o just indicates
        // that the SHA3 core did a full operation. This might be related to the prefix or the
        // message.
        if (absorbed == prim_mubi_pkg::MuBi4True) begin
          kmac_reduced_tb_state_d = DONE;
        end
      end

      DONE: begin
        // Send a Done pulse to trigger wiping the state.
        done = prim_mubi_pkg::MuBi4True;
        kmac_reduced_tb_state_d = FINISH;
      end

      FINISH: begin
        // Wait for the SHA3 FSM to enter the idle state again after wiping before signaling the
        // end of the simulation.
        if (sha3_fsm == StIdle) begin
          test_done = 1'b1;
        end
      end

      default: begin
        kmac_reduced_tb_state_d = FINISH;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_fsm
    if (!rst_ni) begin
      kmac_reduced_tb_state_q <= IDLE;
    end else begin
      kmac_reduced_tb_state_q <= kmac_reduced_tb_state_d;
    end
  end

  // Check responses, signal end of simulation
  always_ff @(posedge clk_i or negedge rst_ni) begin : tb_ctrl
    test_done_o   <= 1'b0;
    test_passed_o <= 1'b0;

    if (rst_ni && (kmac_reduced_tb_state_q != IDLE)) begin
      if (error) begin
        $display("\nERROR: error condition detected.");
        test_done_o   <= 1'b1;
      end else if (test_done) begin
        test_done_o   <= 1'b1;
        if (dpi_digest_bytes_q == output_digest_bytes) begin
          $display("\nSUCCESS: processing finished successfully, output matches expected digest.");
          $display("Expected: %h", dpi_digest_bytes_packed);
          $display("Got:      %h", output_digest_bytes_packed);
          test_passed_o <= 1'b1;
        end else begin
          $display("\nERROR: processing finished, but output doesn't matches expected digest.");
          $display("Expected: %h", dpi_digest_bytes_packed);
          $display("Got:      %h", output_digest_bytes_packed);
          $display("\nInput:    %h", input_msg_bytes_packed);
          test_passed_o <= 1'b0;
        end
      end
    end

    if (count_q == 10'd500) begin
      $display("\nERROR: Simulation timed out.");
      test_done_o <= 1'b1;
    end
  end

  // DUT checking
  // The DUT takes and produces packed SV arrays which are simply organized as follows:
  //
  // MSB .......................... LSB
  // 127 ............................ 0
  //
  // The checked values are byte strings organized as follows:
  // Byte 0, Byte 1, Byte 2, ... Byte 15
  //
  // The functions below can be used for the conversion.
  typedef logic [7:0] msg_bytes_t [MsgLen/8-1:0];
  function automatic msg_bytes_t msg_bits_to_bytes(logic [MsgLen-1:0] bits);
    msg_bytes_t bytes;
    for (int i = 0; i < MsgLen/8; i++) begin
      bytes[i] = bits[i*8 +: 8];
    end
    return bytes;
  endfunction
  function automatic logic [MsgLen-1:0] msg_bits_to_bytes_packed(logic [MsgLen-1:0] bits);
    logic [MsgLen-1:0] bytes;
    for (int i = 0; i < MsgLen/8; i++) begin
      bytes[MsgLen-1 - 8*i -: 8] = bits[i*8 +: 8];
    end
    return bytes;
  endfunction

  typedef logic [7:0] digest_bytes_t [DigestLenBytes-1:0];
  function automatic digest_bytes_t digest_bits_to_bytes(logic [DigestLen-1:0] bits);
    digest_bytes_t bytes;
    for (int i = 0; i < DigestLenBytes; i++) begin
      bytes[i] = bits[i*8 +: 8];
    end
    return bytes;
  endfunction
  function automatic logic [DigestLen-1:0] digest_bits_to_bytes_packed(logic [DigestLen-1:0] bits);
    logic [DigestLen-1:0] bytes;
    for (int i = 0; i < DigestLenBytes; i++) begin
      bytes[DigestLen-1 - 8*i -: 8] = bits[i*8 +: 8];
    end
    return bytes;
  endfunction
  function automatic logic [DigestLen-1:0] digest_bytes_to_bytes_packed(digest_bytes_t bytes);
    logic [DigestLen-1:0] bytes_packed;
    for (int i = 0; i < DigestLenBytes; i++) begin
      bytes_packed[DigestLen-1 - 8*i -: 8] = bytes[i];
    end
    return bytes_packed;
  endfunction

  // Buffer input and output.
  logic [MsgLen-1:0] input_msg;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_input_msg
    if (!rst_ni) begin
      input_msg <= '0;
    end else if (msg_handshake) begin
      input_msg <= msg[0] ^ msg[1];
    end
  end

  logic [DigestLen-1:0] output_digest;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_output_digest
    if (!rst_ni) begin
      output_digest <= '0;
    end else if (state_valid) begin
      output_digest <= state[0][DigestLen-1:0] ^ state[1][DigestLen-1:0];
    end
  end

  // Compute the expected output.
  digest_bytes_t dpi_digest_bytes_d, dpi_digest_bytes_q;
  always_comb begin
    dpi_digest_bytes_d = '{default: '0};
    if (sha3_process) begin
      digestpp_dpi_pkg::c_dpi_sha3_256(input_msg_bytes, {32'b0, MsgLen/8}, dpi_digest_bytes_d);
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_dpi_digest
    if (!rst_ni) begin
      dpi_digest_bytes_q <= '{default: '0};
    end else if (sha3_process) begin
      dpi_digest_bytes_q <= dpi_digest_bytes_d;
    end
  end

  // Various conversions for convenience
  msg_bytes_t input_msg_bytes;
  logic [MsgLen-1:0] input_msg_bytes_packed;
  assign input_msg_bytes = msg_bits_to_bytes(input_msg);
  assign input_msg_bytes_packed = msg_bits_to_bytes_packed(input_msg);

  digest_bytes_t output_digest_bytes;
  logic [DigestLen-1:0] output_digest_bytes_packed;
  assign output_digest_bytes = digest_bits_to_bytes(output_digest);
  assign output_digest_bytes_packed = digest_bits_to_bytes_packed(output_digest);

  logic [DigestLen-1:0] dpi_digest_bytes_packed;
  assign dpi_digest_bytes_packed = digest_bytes_to_bytes_packed(dpi_digest_bytes_q);

endmodule
