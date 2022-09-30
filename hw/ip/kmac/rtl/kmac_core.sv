// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC control and padding logic

`include "prim_assert.sv"

module kmac_core
  import kmac_pkg::*;
#(
  // EnMasking: Enable masking security hardening inside keccak_round
  // If it is enabled, the result digest will be two set of 1600bit.
  parameter  bit EnMasking = 0,
  localparam int Share = (EnMasking) ? 2 : 1 // derived parameter
) (
  input clk_i,
  input rst_ni,

  // From Message FIFO
  input                fifo_valid_i,
  input [MsgWidth-1:0] fifo_data_i [Share],
  input [MsgStrbW-1:0] fifo_strb_i,
  output logic         fifo_ready_o,

  // to SHA3 Core
  output logic                msg_valid_o,
  output logic [MsgWidth-1:0] msg_data_o  [Share],
  output logic [MsgStrbW-1:0] msg_strb_o,
  input                       msg_ready_i,

  // Configurations

  // If kmac_en is cleared, Core logic doesn't function but forward incoming
  // message to SHA3 core
  input                             kmac_en_i,
  input sha3_pkg::sha3_mode_e       mode_i,
  input sha3_pkg::keccak_strength_e strength_i,

  // Key input from CSR
  input [MaxKeyLen-1:0] key_data_i [Share],
  input key_len_e       key_len_i,

  // Controls : same to SHA3 core
  input start_i,
  input process_i,
  input prim_mubi_pkg::mubi4_t done_i,

  // Control to SHA3 core
  output logic process_o,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  output logic sparse_fsm_error_o,
  output logic key_index_error_o
);

  import sha3_pkg::KeccakMsgAddrW;
  import sha3_pkg::KeccakCountW;
  import sha3_pkg::KeccakRate;
  import sha3_pkg::L128;
  import sha3_pkg::L224;
  import sha3_pkg::L256;
  import sha3_pkg::L384;
  import sha3_pkg::L512;

  /////////////////
  // Definitions //
  /////////////////

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 5 -n 6 \
  //      -s 401658243 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (50.00%)
  //  4: |||||||||||||||| (40.00%)
  //  5: |||| (10.00%)
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 5
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 4
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    StKmacIdle = 6'b011000,

    // Secret Key pushing stage
    // The key is sliced by prim_slicer. This state pushes the sliced data into
    // SHA3 hashing engine. When it hits the block size limit,
    // (same as in sha3pad) the state machine moves to Message.
    StKey = 6'b010111,

    // Incoming Message
    // The core does nothing but forwarding the incoming message to SHA3 hashing
    // engine by turning off `en_kmac_datapath`.
    StKmacMsg = 6'b001110,

    // Wait till done signal
    StKmacFlush = 6'b101011,

    // Terminal Error
    StTerminalError = 6'b100000
  } kmac_st_e ;

  /////////////
  // Signals //
  /////////////

  // represents encode_string(K)
  logic [MaxEncodedKeyW-1:0] encoded_key [Share];

  // Key slice address
  // This signal controls the 64 bit output of the sliced secret_key.
  logic [sha3_pkg::KeccakMsgAddrW-1:0] key_index;
  logic inc_keyidx, clr_keyidx;

  // `sent_blocksize` indicates that the encoded key is sent to sha3 hashing
  // engine. If this hits at StKey stage, the state moves to message state.
  logic [sha3_pkg::KeccakCountW-1:0] block_addr_limit;
  logic sent_blocksize;

  // Internal message signals
  logic                kmac_valid       ;
  logic [MsgWidth-1:0] kmac_data [Share];
  logic [MsgStrbW-1:0] kmac_strb        ;

  // Control SHA3 core
  // `kmac_process` is to forward the process signal to SHA3 core only after
  // the KMAC core writes the key block in case of the message is empty.
  // If the incoming message is empty, there's chance that the `process_i`
  // signal can be asserted while KMAC core processing the key block.
  logic kmac_process, process_latched;

  // Indication of Secret key write stage. Only in this stage, the internal
  // message interface is active.
  logic en_key_write;
  logic en_kmac_datapath;

  // Encoded key has wider bits. `key_sliced` is the data to send to sha3
  logic [MsgWidth-1:0] key_sliced [Share];

  sha3_pkg::sha3_mode_e unused_mode;
  assign unused_mode = mode_i;

  /////////
  // FSM //
  /////////
  kmac_st_e st, st_d;

  // State register
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, st_d, st, kmac_st_e, StKmacIdle)

  // Next state and output logic
  // SEC_CM: FSM.SPARSE
  always_comb begin
    st_d = st;

    en_kmac_datapath = 1'b 0;
    en_key_write = 1'b 0;

    clr_keyidx = 1'b 0;

    kmac_valid = 1'b 0;
    kmac_process = 1'b 0;

    sparse_fsm_error_o = 1'b 0;

    unique case (st)
      StKmacIdle: begin
        if (kmac_en_i && start_i) begin
          st_d = StKey;
        end else begin
          st_d = StKmacIdle;
        end
      end

      // If State enters here, regardless of the `process_i`, the state writes
      // full block size of the key into SHA3 hashing engine.
      StKey: begin
        en_kmac_datapath = 1'b 1;
        en_key_write = 1'b 1;

        if (sent_blocksize) begin
          st_d = StKmacMsg;

          kmac_valid = 1'b 0;
          clr_keyidx = 1'b 1;
        end else begin
          st_d = StKey;

          kmac_valid = 1'b 1;
        end
      end

      StKmacMsg: begin
        // If process is previously latched, it is sent to SHA3 here.
        if (process_i || process_latched) begin
          st_d = StKmacFlush;

          kmac_process = 1'b 1;
        end else begin
          st_d = StKmacMsg;
        end
      end

      StKmacFlush: begin
        if (prim_mubi_pkg::mubi4_test_true_strict(done_i)) begin
          st_d = StKmacIdle;
        end else begin
          st_d = StKmacFlush;
        end
      end

      StTerminalError: begin
        // this state is terminal
        st_d = st;
        sparse_fsm_error_o = 1'b 1;
      end

      default: begin
        // this state is terminal
        st_d = StTerminalError;
        sparse_fsm_error_o = 1'b 1;
      end
    endcase

    // SEC_CM: FSM.GLOBAL_ESC, FSM.LOCAL_ESC
    // Unconditionally jump into the terminal error state
    // if the life cycle controller triggers an escalation.
    if (lc_escalate_en_i != lc_ctrl_pkg::Off) begin
      st_d = StTerminalError;
    end
  end

  //////////////
  // Datapath //
  //////////////

  // DATA Mux depending on kmac_en
  // When Key write happens, hold the FIFO request. so fifo_ready_o is tied to 0
  assign msg_valid_o  = (en_kmac_datapath) ? kmac_valid : fifo_valid_i;
  assign msg_data_o   = (en_kmac_datapath) ? kmac_data  : fifo_data_i ;
  assign msg_strb_o   = (en_kmac_datapath) ? kmac_strb  : fifo_strb_i ;
  assign fifo_ready_o = (en_kmac_datapath) ? 1'b 0      : msg_ready_i ;

  // secret key write request to SHA3 hashing engine is always full width write.
  // KeyMgr is fixed 256 bit output. So `right_encode(256)` is 0x020100 --> strb 3
  assign kmac_strb = (en_key_write ) ? '1 : '0;

  assign kmac_data = (en_key_write) ? key_sliced : '{default:'0};

  // Process is controlled by the KMAC core always.
  // This is mainly to prevent process_i asserted while KMAC core is writing
  // the secret key to SHA3 hashing engine (the empty message case)
  assign process_o = (kmac_en_i) ? kmac_process : process_i ;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      process_latched <= 1'b 0;
    end else if (process_i && !process_o) begin
      process_latched <= 1'b 1;
    end else if (process_o ||
      prim_mubi_pkg::mubi4_test_true_strict(done_i)) begin
      process_latched <= 1'b 0;
    end
  end

  // bytepad(encode_string(K), 168 or 136) =====================================
  // 1. Prepare left_encode(w)
  // 2. Prepare left_encode(len(secret_key))
  // 3. Concatenate left_encode(len(secret_key)) || secret_key
  // 4. Concaatenate left_encode(w) || encode_string(secret_key)
  // 5. Based on the address, slice out the data into MsgWidth bits

  // left_encode(w): Same as used in sha3pad logic.
  logic [15:0] encode_bytepad;
  assign encode_bytepad = sha3_pkg::encode_bytepad_len(strength_i);

  // left_encode(len(secret_key))
  // encoded length is always byte size. Use MaxEncodedKeyLenByte parameter
  // from kmac_pkg and add one more byte to indicate how many bytes used to
  // represent len(secret_key)
  // Note that if the secret_key is 128 bit, only lower 16 bits of
  // `encode_keylen` are valid. Refer `encoded_key` concatenation logic below.
  // As the encoded string in the spec big-endian, The endian swap is a must.
  logic [MaxEncodedKeyLenSize + 8 - 1:0] encode_keylen [Share];

  always_comb begin
    // the spec mentioned the key length is encoded in left_encode()
    // The number is represented in big-endian. For example:
    // 384 ==> 0x02 0x01 0x80
    // The first byte is the number of bytes to represent 384
    // The second byte represents 2**8 number, which is 256 here.
    // The third byte represents 2**0 number, which is 128.
    // The data put into MsgFIFO is little-endian and SHA3(Keccak) processes in
    // little-endian. So, below keylen swaps the byte order
    unique case (key_len_i)
      //                           endian-swapped key_length          num_bytes
      // Key128: encode_keylen[0] = {{<<8{MaxEncodedKeyLenSize'(128)}}, 8'h 01};
      // Key192: encode_keylen[0] = {{<<8{MaxEncodedKeyLenSize'(192)}}, 8'h 01};
      // Key256: encode_keylen[0] = {{<<8{MaxEncodedKeyLenSize'(256)}}, 8'h 02};
      // Key384: encode_keylen[0] = {{<<8{MaxEncodedKeyLenSize'(384)}}, 8'h 02};
      // Key512: encode_keylen[0] = {{<<8{MaxEncodedKeyLenSize'(512)}}, 8'h 02};

      // Vivado does not support stream swap for non context value. So assign
      // the value directly.
      Key128: encode_keylen[0] = (MaxEncodedKeyLenSize+8)'('h 0080_01);
      Key192: encode_keylen[0] = (MaxEncodedKeyLenSize+8)'('h 00C0_01);
      Key256: encode_keylen[0] = (MaxEncodedKeyLenSize+8)'('h 0001_02);
      Key384: encode_keylen[0] = (MaxEncodedKeyLenSize+8)'('h 8001_02);
      Key512: encode_keylen[0] = (MaxEncodedKeyLenSize+8)'('h 0002_02);
      default: encode_keylen[0] = '0;
    endcase
  end

  if (EnMasking) begin: gen_encode_keylen_masked
    assign encode_keylen[1] = '0;
  end

  // encode_string(secret_key): Concatenate key
  // Based on the left_encode(len(secret_key)) size, the concatenation logic
  // should be changed. If key length is 128 bit, only lower 16 bits of the
  // encoded length are used so that the upper 8 bits are padded with 0 as
  // defined in bytepad() function.

  for (genvar i = 0 ; i < Share; i++) begin : gen_encoded_key
    always_comb begin
      unique case (key_len_i)
        // In Key 128, 192 case, only lower parts of encode_keylen signal is
        // used. So upper padding requires 8 more bits than MaxKeyLen - keylen
        Key128: encoded_key[i] = {(8 + MaxKeyLen - 128)'(0),
                                  key_data_i[i][0+:128],
                                  encode_keylen[i][0+:MaxEncodedKeyLenSize]};

        Key192: encoded_key[i] = {(8 + MaxKeyLen - 192)'(0),
                                  key_data_i[i][0+:192],
                                  encode_keylen[i][0+:MaxEncodedKeyLenSize]};

        Key256: encoded_key[i] = {(MaxKeyLen - 256)'(0),
                                  key_data_i[i][0+:256],
                                  encode_keylen[i]};

        Key384: encoded_key[i] = {(MaxKeyLen - 384)'(0),
                                  key_data_i[i][0+:384],
                                  encode_keylen[i]};

        // Assume 512bit is the MaxKeyLen
        Key512: encoded_key[i] = {key_data_i[i][0+:512],
                                  encode_keylen[i]};

        default: encoded_key[i] = '0;
      endcase
    end
  end : gen_encoded_key

  // Above logic assumes MaxKeyLen as 512 bits. Revise if it is not.
  `ASSERT_INIT(MaxKeyLenMatchToKey512_A, kmac_pkg::MaxKeyLen == 512)

  // Combine the bytepad `left_encode(w)` and the `encode_string(secret_key)`
  logic [MaxEncodedKeyW + 16 -1 :0] encoded_key_block [Share];

  assign encoded_key_block[0] = {encoded_key[0], encode_bytepad};

  if (EnMasking) begin : gen_encoded_key_block_masked
    assign encoded_key_block[1] = {encoded_key[1], 16'h 0};
  end

  // Slicer to slice out 64 bits
  for (genvar i = 0 ; i < Share ; i++) begin : gen_key_slicer
    prim_slicer #(
      .InW (MaxEncodedKeyW+16),
      .IndexW(KeccakMsgAddrW),
      .OutW(MsgWidth)
    ) u_key_slicer (
      .sel_i  (key_index),
      .data_i (encoded_key_block[i]),
      .data_o (key_sliced[i])
    );
  end

  // `key_index` logic
  // key_index is used to select MsgWidth data from long `encoded_key_block`
  // It behaves same as `keccak_addr` or `prefix_index` in sha3pad module.
  assign inc_keyidx = kmac_valid & msg_ready_i ;

  // This primitive is used to place a hardened counter
  // SEC_CM: CTR.REDUN
  prim_count #(
    .Width(sha3_pkg::KeccakMsgAddrW)
  ) u_key_index_count (
    .clk_i,
    .rst_ni,
    .clr_i(clr_keyidx),
    .set_i(1'b0),
    .set_cnt_i('0),
    .incr_en_i(inc_keyidx),
    .decr_en_i(1'b0),
    .step_i(sha3_pkg::KeccakMsgAddrW'(1)),
    .cnt_o(key_index),
    .cnt_next_o(),
    .err_o(key_index_error_o)
  );

  // Block size based on the address.
  // This is used for bytepad() and also pad10*1()
  // assign block_addr_limit = KeccakRate[strength_i];
  // but below is easier to understand
  always_comb begin
    unique case (strength_i)
      L128: block_addr_limit = KeccakCountW'(KeccakRate[L128]);
      L224: block_addr_limit = KeccakCountW'(KeccakRate[L224]);
      L256: block_addr_limit = KeccakCountW'(KeccakRate[L256]);
      L384: block_addr_limit = KeccakCountW'(KeccakRate[L384]);
      L512: block_addr_limit = KeccakCountW'(KeccakRate[L512]);

      default: block_addr_limit = '0;
    endcase
  end

  assign sent_blocksize = (key_index == block_addr_limit);


  // Encoded Output Length =====================================================
  //
  // KMAC(K,X,L,S) := cSHAKE(newX,L,"KMAC",S)
  //   K : Secret Key
  //   X : Input Message
  //   L : Output Length
  //   S : Customization input string
  //   newX = bytepad(encode_string(key), 168or136) || X || right_encode(L)
  //
  // Software writes desired output length as encoded value into the message
  // FIFO at the end of the message prior to set !!CMD.process.


  ////////////////
  // Assertions //
  ////////////////

  // If process_latched is set, then at Message state, it should be cleared

  `ASSERT(ProcessLatchedCleared_A,
          st == StKmacMsg && process_latched |=> !process_latched)

  // Assume configuration is stable during the operation
  `ASSUME(KmacEnStable_M, $changed(kmac_en_i) |-> st inside {StKmacIdle, StTerminalError})
  `ASSUME(ModeStable_M, $changed(mode_i) |-> st inside {StKmacIdle, StTerminalError})
  `ASSUME(StrengthStable_M,
          $changed(strength_i) |->
          (st inside {StKmacIdle, StTerminalError}) ||
          ($past(st) == StKmacIdle))
  `ASSUME(KeyLengthStable_M,
          $changed(key_len_i) |->
          (st inside {StKmacIdle, StTerminalError}) ||
          ($past(st) == StKmacIdle))
  `ASSUME(KeyDataStable_M,
          $changed(key_data_i) |->
          (st inside {StKmacIdle, StTerminalError}) ||
          ($past(st) == StKmacIdle))

  // no acked to MsgFIFO in StKmacMsg
  `ASSERT(AckOnlyInMessageState_A,
          fifo_valid_i && fifo_ready_o && kmac_en_i |-> st == StKmacMsg)

endmodule : kmac_core
