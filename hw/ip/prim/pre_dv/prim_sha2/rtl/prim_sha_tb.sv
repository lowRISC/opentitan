// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SHA-2 256 (MultimodeEn = 0) hash engine testbench
//
// This testbench is used to perform basic verification of the SHA-2 256 hash engine and
// to scope an understanding for the requirements for interfacing with the engine.

// The testbench instantiates the 32-bit SHA-2 256 engine and tests a subset of
// test vectors and the digest output against the expected hash.

module prim_sha_tb (
  input logic clk_i,
  input logic rst_ni,

  output logic test_done_o,
  output logic test_passed_o
  );

  import prim_sha2_pkg::*;
  // DUT signals
  logic              valid_in;
  sha_fifo32_t       data_in;
  logic              sha_en, hash_start, ready_out;
  logic              hash_process;
  logic [63:0]       msg_length; // 64-bit message length
  sha_word64_t [7:0] digest;
  logic              idle;

  // Instantiate SHA-2 256 multi-mode engine
  prim_sha2_32 #(
      .MultimodeEn(0)
  ) u_prim_sha2_256 (
    .clk_i (clk_i),
    .rst_ni (rst_ni),

    .wipe_secret        (1'b0),
    .wipe_v             (32'b0),
    .fifo_rvalid        (valid_in),
    .fifo_rdata         (data_in),
    .fifo_rready        (ready_out),
    .sha_en             (sha_en),
    .hash_start         (hash_start),
    .digest_mode        (2'b00), //unused port
    .hash_process       (hash_process),
    .hash_done          (hash_done_d),
    .message_length     ({{64'b0},msg_length}),
    .digest             (digest),
    .idle               (idle)
  );

  // TB signals
  typedef enum {
    HASH_INIT,
    HASH_START,
    HASH_INPROGRESS,
    HASH_FINALIZE,
    HASH_WAIT,
    HASH_END
  } sha2_tb_e;
  sha2_tb_e  sha2_tb_state_d, sha2_tb_state_q;

  localparam int MsgCount     = 8;    // set this to number of test vectors
  localparam int MaxWordCount = 1022; // set this to max word count in longest message

  localparam int ProcessDelayCycles  = 10;  // set this to # of delay cycles until process = 1
  localparam int WordDelayCycles     = 0;   // set this to # of delay cycles between each word input

  typedef struct packed {
    int                             msg_length; // # of bits
    sha_word32_t [MaxWordCount-1:0] msg_input;
    sha_word32_t [MaxWordCount-1:0] msg_parsed;
    sha_word32_t [7:0]              expectedHash;
  } test_vector_t;

  test_vector_t [MsgCount-1:0] test_vectors;

  int current_msg_length;
  int msg_counter_q, msg_counter_d;
  int delay_process_counter_q, delay_process_counter_d; // to track stall until process = 1
  int delay_word_counter_q, delay_word_counter_d;       // to track stall until next word is fed
  int word_counter_q, word_counter_d;
  int correct_counter_q, correct_counter_d;

  logic msg_counter_increment, word_counter_increment, word_counter_reset;
  logic hash_done_q, hash_done_d, hash_correct;
  logic disable_delay_word_d, disable_delay_word_q;

  initial begin: message_feeding
    // Selected subset of test vectors from the NIST SHA test vectors
    // https://csrc.nist.gov/Projects/cryptographic-algorithm-validation-program/Secure-Hashing#shavs

    int i = 0;
    // SHA-2 256 short msg (word-aligned)
    test_vectors[i].msg_length        = 256;
    test_vectors[i].msg_input         = 256'h09fc1accc230a205e4a208e64a8f204291f581a12756392da4b8c0cf5ef02b95;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'h4f44c1c7fbebb6f9601829f3897bfd650c56fa07844be76489076356ac1886a4;

    #1 i = i + 1;

    // SHA-256 short msg (word-aligned)
    test_vectors[i].msg_length        = 288;
    test_vectors[i].msg_input         = 288'h4e3d8ac36d61d9e51480831155b253b37969fe7ef49db3b39926f3a00b69a36774366000;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'hbf9d5e5b5393053f055b380baed7e792ae85ad37c0ada5fd4519542ccc461cf3;

    #1 i = i + 1;

    // SHA-256 short msg (word-aligned)
    test_vectors[i].msg_length        = 32;
    test_vectors[i].msg_input         = 32'h74ba2521;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'hb16aa56be3880d18cd41e68384cf1ec8c17680c45a02b1575dc1518923ae8b0e;

    #1 i = i + 1;

    // SHA-2 256 long msg (word-aligned)
    test_vectors[i].msg_length        = 6848;
    test_vectors[i].msg_input         = 6848'h9c4bdc3b1af6ab9dc7bd2dd90e2e429a07d5dd5c48bb7016fe2ca51d3cbd4f45928ea049e2cd9c6d6f7bcd613773396983a891bbbcaeab28807c32fff5709d2f5d935dabeb1f5b13d53ea190ab155700e701f253c520a834551427ecce03868425e27c2adef4d0d7238d102e131c86a65c6868eb0c1a4f82a47ceaac6e80f48e1104638e6354e3007ef182021691ada40a665b4d38a3885a963de5077feece934a807c9f21487cd810f15fd55d7bb4421882333ff2c43b0353de7fc5a656fcdcf8de2e25c1d783a50115106f8fe282c8ae45588ae28450c602e71fad8dbf65b141a7e0e7ea0ae0b079e5fb9855ce017ef63633f6afebafebcbe02f89dc31f3595062fcae45e87b419fea8918574818ac15dd2a4a020141bad752161f3bb58d1e4b97e9427a793c9f9bab22b63c57af9936c2a65082cfec7a4ec53c3750511b465bcf0f6b30c50c1496b02f3bad04af8e7f6e10ced85c997558bf099bc60f861aa790d6f10fd5d1e6b88216705156fed31868ce8dabb031f11bcae51243f7b4e25865a69bc1b0755e28a8411ad15585b02a384a55a4d49a37c26d38636f108ee695d3e732eb5edec40faa1604d4092c6ddd67eaed6bcfbe8f73316a57f462fc6d8764017f38e8f6609411fff5037bdc51587c181fa7a98340569ce3b677f5e7c1559f5c474d55a379e06463b406b27ba5c4ff3bb1006bd39495380b48a3d23528280c6055d5adcf591a2baa0a84b6f2b14878ba6c201c95d1558d4bd41d00d0eb2834767076f861466bef3bbf25902abd0d70ff18acc4b140c121092490879e527c9e045fd83f4189fb36809b92470a113b6f717d4f6b0e29fe7faefea27089a44dd274eba48a576af18be06673e379f5f9fb7862af1a96d4372ca32bfbc2782bc2592cdc82df8b307573c3e76f6d61b06f9e7c9174d9308892b14f734485522d04ba96fa1948c525b17891e72feca98bc6dfe5d047aec48f3797199d25c101f33a7d180c12cced8fca21b32e5b6839ce26461ce8d0a33b2f4f666b73457f6cc58d2b1cdc1473ebb7ebf68f849ae9f9c1b65c87a1b6bf7bb102a4acbb4dc77bea254b0930c846a7e53a808eb19478d1ab9fa88fc2a10a6d5d77db433ee49f16ac296547d1d64c0961df46187cf21ca9d608b39c153b8df97ad7929ac4b3112551c2023e87e58efa7203d196ae5cde69881a031760294f0852;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'hf574ac85532bc0c6c4e7614a2e084dbc49fbc474cda593144af28c5cc5f293f8;

    #1 i = i + 1;

    // SHA-2 256 short msg (word-aligned)
    test_vectors[i].msg_length        = 512;
    test_vectors[i].msg_input         = 512'h5a86b737eaea8ee976a0a24da63e7ed7eefad18a101c1211e2b3650c5187c2a8a650547208251f6d4237e661c7bf4c77f335390394c37fa1a9f9be836ac28509;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'h42e61e174fbb3897d6dd6cef3dd2802fe67b331953b06114a65c772859dfc1aa;

    #1 i = i + 1;

    // SHA-2 256 short msg (not word-aligned)
    test_vectors[i].msg_length        = 40;
    // msg is padded at the end with zeros and number of bits are adjusted (should be 40)
    test_vectors[i].msg_input         = 64'hc299209682000000;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'hf0887fe961c9cd3beab957e8222494abb969b1ce4c6557976df8b0f6d20e9166;

    #1 i = i + 1;

    // SHA-2 256 short msg (512+32 = 544)
    test_vectors[i].msg_length        = 544;
    test_vectors[i].msg_input         = 544'h5a86b737eaea8ee976a0a24da63e7ed7eefad18a101c1211e2b3650c5187c2a8a650547208251f6d4237e661c7bf4c77f335390394c37fa1a9f9be836ac28509ab801234;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'h44a2d734e1b61bc487c4ece0aaae5996db07481b0b776202da5b77b7f45dd86e;

    #1 i = i + 1;

    // SHA-2 256 short msg word-aligned
    test_vectors[i].msg_length        = 32;
    test_vectors[i].msg_input         = 32'h00000001;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'hb40711a88c7039756fb8a73827eabe2c0fe5a0346ca7e0a104adc0fc764f528d;

  end

  function automatic sha_word32_t [MaxWordCount-1:0] swap_words (test_vector_t sha_test_vector);
    automatic bit offset;
    if (sha_test_vector.msg_length % 32 == 0)  offset = 0;
    else                                       offset = 1;

    for (int i = 0; i < sha_test_vector.msg_length/32 + offset; i++) begin
        swap_words[i] = sha_test_vector.msg_input[(sha_test_vector.msg_length/32) - !offset - i];
    end
  endfunction : swap_words

  always_comb begin : hash_engine_tb_fsm
    // DUT
    hash_start                 = 1'b0;
    sha_en                     = 1'b0;
    hash_process               = 1'b0;
    valid_in                   = 1'b0;
    msg_length                 = 64'b0;
    current_msg_length         = (word_counter_q  + 1) * 32; // 32-bit words
    data_in.mask               = 4'hF;
    data_in.data               = 32'h0000;

    // TB
    msg_counter_increment      = 1'b0;
    word_counter_increment     = 1'b0;
    word_counter_reset         = 1'b0;
    hash_correct               = 1'b0;
    sha2_tb_state_d            = sha2_tb_state_q;
    delay_process_counter_d    = delay_process_counter_q;
    delay_word_counter_d       = delay_word_counter_q;
    correct_counter_d          = correct_counter_q;
    disable_delay_word_d       = disable_delay_word_q;

    test_done_o   = 1'b0;
    test_passed_o = 1'b0;

    unique case (sha2_tb_state_q)
      HASH_INIT: begin
        word_counter_reset = 1'b1;
        sha_en = 1'b0; // deasserts the engine to reset its state
        // Check that engine is idle before enabling it
        if (idle == 1'b1) sha2_tb_state_d =  HASH_START;
      end
      HASH_START: begin
        sha_en                = 1'b1; // enables the hash engine:
        hash_start            = 1'b1; // only one pulse to start hashing a complete message
        msg_length            = 64'(test_vectors[msg_counter_q].msg_length);
        word_counter_reset    = 1'b1; // reset word counter for new message
        delay_word_counter_d  = 0;   // reset delay word counter
        disable_delay_word_d  = 1'b0;
        sha2_tb_state_d       = HASH_INPROGRESS;
        /*// block to test engine reset and recovery: plug this at different points of hashing
        if (msg_counter_q == 9) begin // try different messages
            sha2_tb_state_d =  HASH_START;
            msg_counter_increment = 1'b1;
        end*/
      end
      HASH_INPROGRESS: begin
        sha_en   = 1'b1;
        delay_word_counter_d = delay_word_counter_q + 1;
        msg_length           = 64'(test_vectors[msg_counter_q].msg_length);

        if ((delay_word_counter_q == WordDelayCycles) && !disable_delay_word_q) begin
          valid_in             = 1'b1; // indicates valid message input for the hashing engine
          data_in.data         = test_vectors[msg_counter_q].msg_parsed[word_counter_q];
          delay_word_counter_d = 0; // reset delay counter
          if (ready_out) word_counter_increment = 1'b1; // word has been absorbed so increment
          if (current_msg_length >= test_vectors[msg_counter_q].msg_length) begin
            disable_delay_word_d = 1'b1;
            msg_length           = 64'(test_vectors[msg_counter_q].msg_length);
            // uncomment to assert here or delay by at least 1 cycle (ProcessDelayCycles)
            // in HASH_FINALIZE
            // hash_process = 1'b1;
            if (current_msg_length > test_vectors[msg_counter_q].msg_length) begin
              // non-aligned messages
              data_in.mask                  = 4'b1000;   // byte masking for non-aligned messages
              delay_process_counter_d       = 0;             // reset delay cycles count
              // sha2_tb_state_d            = HASH_INPROGRESS; // assert valid_in for another cycle
              sha2_tb_state_d               = HASH_FINALIZE; // do not reset word counter just yet
            end else if (current_msg_length == test_vectors[msg_counter_q].msg_length) begin
              if (ready_out) begin // final word consumed
                delay_process_counter_d = 0;    // reset delay cycles count
                // sha2_tb_state_d      = HASH_WAIT;
                sha2_tb_state_d         = HASH_FINALIZE;
                word_counter_reset      = 1'b1;
              end else begin
                sha2_tb_state_d         = HASH_INPROGRESS;
              end
            end
          end else begin
              sha2_tb_state_d    = HASH_INPROGRESS;
          end
        end else begin
          data_in.data  = test_vectors[msg_counter_q].msg_parsed[word_counter_q];
          if ((current_msg_length >= test_vectors[msg_counter_q].msg_length)
              && disable_delay_word_q) begin
            msg_length = 64'(test_vectors[msg_counter_q].msg_length);
            valid_in   = 1'b1; // indicates valid message input for the hashing engine
            if (current_msg_length > test_vectors[msg_counter_q].msg_parsed[word_counter_q]) begin
              data_in.mask               = 4'b1000;   // byte masking for non-aligned messages
            end
              if (ready_out) begin
                delay_process_counter_d    = 0; // reset delay cycles count
                delay_word_counter_d       = 0; // reset delay word counter
                //sha2_tb_state_d            = HASH_WAIT;
                sha2_tb_state_d          = HASH_FINALIZE;
                word_counter_reset         = 1'b1;
              end
          end else begin
            sha2_tb_state_d = HASH_INPROGRESS;
          end
        end
      end
      HASH_FINALIZE: begin // to test delay cycles until hash_process is fed
        data_in.data             = test_vectors[msg_counter_q].msg_parsed[word_counter_q];
        word_counter_reset       = 1'b1;
        sha_en                   = 1'b1;
        delay_process_counter_d  = delay_process_counter_q + 1;
        // feed message length fed at most 1 clock cycle later and keep it fed
        msg_length               = 64'(test_vectors[msg_counter_q].msg_length);
        if (delay_process_counter_q == ProcessDelayCycles) begin
          hash_process    = 1'b1;
          sha2_tb_state_d = HASH_WAIT;
        end else begin
          sha2_tb_state_d = HASH_FINALIZE;
        end
      end
      HASH_WAIT: begin
        sha_en     = 1'b1;
        msg_length = 64'(test_vectors[msg_counter_q].msg_length);
        if (hash_done_q == 1'b1) begin
            hash_correct = ({digest [0][31:0], digest [1][31:0], digest [2][31:0],
                             digest [3][31:0], digest [4][31:0], digest [5][31:0],
                             digest [6][31:0], digest [7][31:0]} ==
                             test_vectors[msg_counter_q].expectedHash[7:0]);

          correct_counter_d     = hash_correct ? correct_counter_q + 1 : correct_counter_q;
          msg_counter_increment = 1'b1;

          if (msg_counter_q == MsgCount - 1) sha2_tb_state_d =  HASH_END; // done with test vectors
          else                               sha2_tb_state_d =  HASH_START;
        end
        else begin
          sha2_tb_state_d = HASH_WAIT;
        end
      end
      HASH_END: begin
        sha_en          = 1'b0;
        test_done_o     = 1'b1;
        // test passes if hash is correct for all test vectors
        test_passed_o   = correct_counter_q == MsgCount ? 1'b1 : 1'b0;
        sha2_tb_state_d = HASH_END;
      end
      default: begin
        sha2_tb_state_d = HASH_END;
      end
    endcase
  end

  // Keep count of test vectors
  assign msg_counter_d = msg_counter_increment ? msg_counter_q + 'b1 : msg_counter_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : msg_count
    if (!rst_ni) msg_counter_q <= '0;
    else         msg_counter_q <= msg_counter_d;
  end

  // Increment and reset word counter
  assign word_counter_d = word_counter_reset     ? '0                   :
                          word_counter_increment ? word_counter_q + 'b1 :
                          word_counter_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : word_count
    if (!rst_ni) word_counter_q <= '0;
    else if (msg_counter_increment) word_counter_q <= '0; // reset for new message
    else word_counter_q <= word_counter_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : delay_process_count
    if (!rst_ni) delay_process_counter_q <= 0;
    else         delay_process_counter_q <= delay_process_counter_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : delay_word_count
    if (!rst_ni) delay_word_counter_q <= 0;
    else         delay_word_counter_q <= delay_word_counter_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : disable_delay_word
    if (!rst_ni) disable_delay_word_q <= 1'b0;
    else         disable_delay_word_q <= disable_delay_word_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : correct_count
    if (!rst_ni) correct_counter_q <= 0;
    else         correct_counter_q <= correct_counter_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_fsm
    if (!rst_ni) sha2_tb_state_q <= HASH_INIT;
    else         sha2_tb_state_q <= sha2_tb_state_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : digest_ctrl
    if (!rst_ni) hash_done_q <= '0;
    else         hash_done_q <= hash_done_d;
  end

endmodule
