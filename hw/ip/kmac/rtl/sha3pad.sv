// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SHA3 padding logic

`include "prim_assert.sv"

module sha3pad
  import sha3_pkg::*;
#(
  parameter  bit EnMasking = 0,
  localparam int Share = (EnMasking) ? 2 : 1
) (
  input clk_i,
  input rst_ni,

  // Message interface (FIFO)
  input                       msg_valid_i,
  input        [MsgWidth-1:0] msg_data_i [Share],
  input        [MsgStrbW-1:0] msg_strb_i,         // one strobe for shares
  output logic                msg_ready_o,

  // N, S: Used in cSHAKE mode only
  input [NSRegisterSize*8-1:0] ns_data_i, // See sha3_pkg for details

  // output to keccak_round: message path
  output logic                       keccak_valid_o,
  output logic [KeccakMsgAddrW-1:0]  keccak_addr_o,
  output logic [MsgWidth-1:0]        keccak_data_o [Share],
  input  logic                       keccak_ready_i,

  // keccak_round control and status
  // `run` initiates the keccak_round to process full keccak_f (24rounds).
  // `complete` is an input from keccak round showing the current keccak_f is
  // completed.
  output logic keccak_run_o,
  input        keccak_complete_i,

  // configurations
  input sha3_mode_e       mode_i,
  // strength_i is used in bytepad operation. bytepad() is used in cSHAKE only.
  // SHA3, SHAKE doesn't have encode_N,S
  input keccak_strength_e strength_i,

  // control signal
  // start_i is a pulse signal triggers the padding logic (and the rest of SHA)
  // to accept the incoming messages. This signal is used in the pad module,
  // to initiate the prefix transmitting to keccak_round
  input start_i,
  // process_i is a pulse signal triggers the pad logic to stop receiving the
  // message from MSG_FIFO and pad the trailing bits specified in the SHA3
  // standard. Look at `funcpad` signal for the values.
  input process_i,
  // done_i is a pulse signal to make the pad logic to clear internal variables
  // and to move back to the Idle state for next hashing process.
  // done_i may not needed if sw controls the keccak_round directly.
  input prim_mubi_pkg::mubi4_t done_i,

  // Indication of the Keccak Sponge Absorbing is complete, it is time for SW to
  // control the Keccak-round if it needs more digest, or complete by asserting
  // `done_i`
  output prim_mubi_pkg::mubi4_t absorbed_o,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  // Indication that there was a fault in the sparse encoding
  output logic sparse_fsm_error_o,

  // Indication that there was a fault in the counter
  output logic msg_count_error_o
);

  /////////////////
  // Definitions //
  /////////////////

  // Padding States
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 10 -n 7 \
  //      -s 1116691466 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (42.22%)
  //  4: |||||||||||||||||| (40.00%)
  //  5: ||||| (11.11%)
  //  6: || (4.44%)
  //  7: | (2.22%)
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 5
  //
  localparam int StateWidthPad = 7;
  typedef enum logic [StateWidthPad-1:0] {
    StPadIdle = 7'b1000010,

    // Sending a block of prefix, if cSHAKE mode is turned on. For the rest
    // (SHA3, SHAKE), sending prefix is not needed. FSM moves from Idle to
    // Message directly in that case.
    //
    // As prim_slicer is instantiated, zerofill after the actual prefix is done
    // by the module.
    StPrefix = 7'b0111100,
    StPrefixWait =7'b1001100,

    // Sending Message. In this state, it directly forwards the incoming data
    // to Keccak round module. If `process_i` is asserted, then the rest of the
    // messages will be discarded until new `start_i` is asserted.
    //
    // The incoming data can be partial write. Padding logic counts the number
    // of bytes received and pause if a block size is transferred.
    StMessage = 7'b0100101,
    StMessageWait = 7'b0001111,

    // After sending the messages, then `process_i` is set, the FSM pads at the
    // end of the message based on `mode_i`. If this is the last byte of the
    // block, then it pads [7] to 1 to complete `pad10*1()` function.
    StPad = 7'b1111010,
    StPadRun = 7'b0011001,

    // If the padding isn't the end of the block byte (which will be rare case),
    // FSM moves to another zerofill state. In contrast to StZerofill, this state
    StPad01 = 7'b1101001,

    // Flushing the internal packers in front of the Keccak data output port.
    StPadFlush = 7'b1010111,

    StTerminalError = 7'b0110011
  } pad_st_e;

  typedef enum logic [2:0] {
    MuxNone    = 3'b 000,
    MuxFifo    = 3'b 001,
    MuxPrefix  = 3'b 010,
    MuxFuncPad = 3'b 011,
    MuxZeroEnd = 3'b 100
  } mux_sel_e;

  ////////////////////
  // Configurations //
  ////////////////////

  logic [KeccakCountW-1:0] block_addr_limit;

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

  /////////////////////
  // Control Signals //
  /////////////////////

  // `sel_mux` selects the output data among the incoming or internally generated data.
  // MuxFifo:    data from external (msg_data_i)
  // MuxPrefix:  bytepad(encode_string(N)||encode_string(S), )
  // MuxFuncPad: function_pad with end of message
  // MuxZeroEnd: all 0
  mux_sel_e sel_mux;

  // `sent_message` indicates the number of entries sent to keccak round per
  // block. The value shall be enough to cover Maximum entry of the Keccak
  // storage as defined in sha3_pkg, `$clog2(KeccakEntries+1)`. Logically,
  // it is not needed to have more than KeccakEntries but for safety in case of
  // SHA3 context switch resuming the SHA3 from the middle of sponge
  // construction. If needed, the software should be able to write whole 1600
  // bits. The `sent_message` is used to check sent_blocksize.
  logic [KeccakCountW-1:0] sent_message;
  logic inc_sentmsg, clr_sentmsg;

  // This primitive is used to place a hardened counter
  // SEC_CM: CTR.REDUN
  prim_count #(
    .Width(KeccakCountW)
  ) u_sentmsg_count (
    .clk_i,
    .rst_ni,
    .clr_i(clr_sentmsg),
    .set_i(1'b0),
    .set_cnt_i(KeccakCountW'(0)),
    .incr_en_i(inc_sentmsg),
    .decr_en_i(1'b0),
    .step_i(KeccakCountW'(1)),
    .cnt_o(sent_message),
    .cnt_next_o(),
    .err_o(msg_count_error_o)
  );


  assign inc_sentmsg = keccak_valid_o & keccak_ready_i ;

  // Prefix index to slice the `prefix` n-bits into multiple of 64bit.
  logic [KeccakMsgAddrW-1:0] prefix_index;
  assign prefix_index = (sent_message < block_addr_limit) ? sent_message : '0;

  // fsm_keccak_valid is an output signal from FSM which to send data generated
  // inside the pad logic to keccak_round
  logic fsm_keccak_valid;

  // hold_msg to prevent message from being forwarded into keccak_round and
  // acked. Mainly the usage is to hold the message and initiates the
  // keccak_round for current block.
  logic hold_msg;

  // latch the partial write. Latched data is used for funcpad_merged
  logic en_msgbuf;
  logic clr_msgbuf;

  ///////////////////
  // State Machine //
  ///////////////////

  // Inputs

  // FSM moves to StPrefix only when cSHAKE is enabled
  logic mode_eq_cshake;
  assign mode_eq_cshake = (mode_i == CShake) ? 1'b 1 : 1'b 0;

  // `sent_blocksize` indicates the pad logic pushed block size data into
  // keccak round logic.
  logic sent_blocksize;

  assign sent_blocksize = (sent_message == block_addr_limit) ? 1'b 1 : 1'b 0;

  // `keccak_ack` indicates the request is accepted in keccak_round
  logic keccak_ack;

  assign keccak_ack = keccak_valid_o & keccak_ready_i ;

  // msg_partial indicates the incoming message is partial write or not.
  // This is used to check if the incoming message need to be latched inside or
  // not. If no partial message is at the end, msg_buf doesn't have to latch
  // msg_data_i. It is assumed that the partial message is permitted only at
  // the end of the message. So if (msg_valid_i && msg_partial && msg_ready_o),
  // there will be no msg_valid_i till process_latched.
  // Shall be used with msg_valid_i together.
  logic msg_partial;
  assign msg_partial = (&msg_strb_i != 1'b 1);


  // `process_latched` latches the `process_i` input before it is seen in the
  // FSM. `process_i` may follow `start_i` too fast so that the FSM may not
  // see it fast enought in case of cSHAKE mode. cSHAKE needs to process the
  // prefix prior to see the process indicator.
  logic process_latched;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      process_latched <= 1'b 0;
    end else if (process_i) begin
      process_latched <= 1'b 1;
    end else if (prim_mubi_pkg::mubi4_test_true_strict(done_i)) begin
      process_latched <= 1'b0;
    end
  end

  // State Register ===========================================================
  pad_st_e st, st_d;

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, st_d, st, pad_st_e, StPadIdle)

  // `end_of_block` indicates current beat is end of the block
  // It shall set when the address reaches to the end of the block. End address
  // is set by the strength_i, which is `block_addr_limit`.
  logic end_of_block;

  assign end_of_block = ((sent_message + 1'b1) == block_addr_limit) ? 1'b 1 : 1'b 0;


  // Next logic and output logic ==============================================
  // SEC_CM: ABSORBED.CTRL.MUBI
  prim_mubi_pkg::mubi4_t absorbed_d;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) absorbed_o <= prim_mubi_pkg::MuBi4False;
    else         absorbed_o <= absorbed_d;
  end

  always_comb begin
    st_d = st;

    // FSM output : default values
    keccak_run_o = 1'b 0;
    sel_mux      = MuxNone;

    fsm_keccak_valid = 1'b 0;

    hold_msg = 1'b 0;
    clr_sentmsg = 1'b 0;

    en_msgbuf = 1'b 0;
    clr_msgbuf = 1'b 0;

    absorbed_d = prim_mubi_pkg::MuBi4False;

    sparse_fsm_error_o = 1'b 0;

    unique case (st)

      // In Idle state, the FSM checks if the software (or upper FSM) initiates
      // the hash process. If `start_i` is asserted (assume it is pulse), FSM
      // starts to push the data into the keccak round logic. Depending on the
      // hashing mode, FSM may push additional prefex in front of the actual
      // message. It means, the message could be back-pressured until the first
      // prefix is processed.
      StPadIdle: begin
        if (start_i) begin
          // If cSHAKE, move to Prefix state
          if (mode_eq_cshake) begin
            st_d = StPrefix;
          end else begin
            st_d = StMessage;
          end
        end else begin
          st_d = StPadIdle;
        end
      end

      // At Prefix state, FSM pushes
      // `bytepad(encode_string(N)||encode_string(S), 168or136)`. The software
      // already prepared `encode_string(N) || encode_string(S)` in the regs.
      // So, the FSM adds 2Byte in front of ns_data_i, which is an encoded
      // block size (see `encoded_bytepad` below)
      // After pushing the prefix, it initiates the hash process and move to
      // Message state.
      StPrefix: begin
        sel_mux = MuxPrefix;

        if (sent_blocksize) begin
          st_d = StPrefixWait;

          keccak_run_o = 1'b 1;
          fsm_keccak_valid = 1'b 0;
          clr_sentmsg = 1'b 1;
        end else begin
          st_d = StPrefix;

          fsm_keccak_valid = 1'b 1;
        end
      end

      StPrefixWait: begin
        sel_mux = MuxPrefix;

        if (keccak_complete_i) begin
          st_d = StMessage;
        end else begin
          st_d = StPrefixWait;
        end
      end

      // Message state pushes the incoming message into keccak round logic.
      // It forwards the message while counting the data and if it reaches
      // the block size, it triggers the keccak round to run. If `process` is
      // set, it moves to Pad state.
      StMessage: begin
        sel_mux = MuxFifo;

        if (msg_valid_i && msg_partial) begin
          st_d = StMessage;

          en_msgbuf = 1'b 1;
        end else if (sent_blocksize) begin
          // Check block completion first even process is set.
          st_d = StMessageWait;

          keccak_run_o = 1'b 1;
          clr_sentmsg = 1'b 1;
          hold_msg = 1'b 1;
        end else if (process_latched || process_i) begin
          st_d = StPad;

          // Not asserting the msg_ready_o
          hold_msg = 1'b 1;
        end else begin
          st_d = StMessage;

        end
      end

      StMessageWait: begin
        hold_msg = 1'b 1;

        if (keccak_complete_i) begin
          st_d = StMessage;
        end else begin
          st_d = StMessageWait;
        end
      end

      // Pad state just pushes the ending suffix. Depending on the mode, the
      // padding value is unique. SHA3 adds 2'b10, SHAKE adds 4'b1111, and
      // cSHAKE adds 2'b 00. Refer `function_pad`. The signal has one more bit
      // defined to accomodate first 1 bit of `pad10*1()` function.
      StPad: begin
        sel_mux = MuxFuncPad;

        fsm_keccak_valid = 1'b 1;

        if (keccak_ack && end_of_block) begin
          // If padding is the last block, don't have to move to StPad01, just
          // run Keccak and complete
          st_d = StPadRun;

          // always clear the latched msgbuf
          clr_msgbuf = 1'b 1;
          clr_sentmsg = 1'b 1;
        end else if (keccak_ack) begin
          st_d = StPad01;
          clr_msgbuf = 1'b 1;
        end else begin
          st_d = StPad;
        end
      end

      StPadRun: begin
        st_d = StPadFlush;

        keccak_run_o = 1'b 1;
        clr_sentmsg = 1'b 1;
      end

      // Pad01 pushes the end bit of pad10*1() function. As keccak accepts byte
      // size only, StPad always pushes partial (5bits). So at this state, it
      // pushes rest of 3bits. If the data pushed in StPad is the last byte of
      // the block, then Pad01 pushes to the same byte, if not, it first
      // zero-fill the block then pad 1 to the end.
      StPad01: begin
        sel_mux = MuxZeroEnd;

        // There's no chance StPad01 can be a start of the block. So can be
        // discard that the sent_blocksize is set at the beginning.
        if (sent_blocksize) begin
          st_d = StPadFlush;

          fsm_keccak_valid = 1'b 0;
          keccak_run_o = 1'b 1;
          clr_sentmsg = 1'b 1;
        end else begin
          st_d = StPad01;

          fsm_keccak_valid = 1'b 1;
        end
      end

      StPadFlush: begin
        // Wait completion from keccak_round or wait SW indicator.
        clr_sentmsg = 1'b 1;
        clr_msgbuf = 1'b 1;

        if (keccak_complete_i) begin
          st_d = StPadIdle;

          absorbed_d = prim_mubi_pkg::MuBi4True;
        end else begin
          st_d = StPadFlush;
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

  // `encode_bytepad` represents the first two bytes of bytepad()
  // It depends on the block size. We can reuse KeccakRate
  // 10000000 || 00010101 // 168
  // 10000000 || 00010001 // 136
  logic [15:0] encode_bytepad;

  assign encode_bytepad = encode_bytepad_len(strength_i);

  // Prefix size ==============================================================
  // Prefix represents bytepad(encode_string(N) || encode_string(S), 168 or 136)
  // encode_string(N) || encode_string(S) is prepared by the software and given
  // through `ns_data_i`. The first part of bytepad is determined by the
  // `strength_i` and stored into `encode_bytepad`.

  // It is assumed that the prefix always smaller than the block size.
  logic [PrefixSize*8-1:0] prefix;

  assign prefix = {ns_data_i, encode_bytepad};

  logic [MsgWidth-1:0] prefix_sliced;
  logic [MsgWidth-1:0] prefix_data [Share];

  prim_slicer #(
    .InW (PrefixSize*8),
    .IndexW(KeccakMsgAddrW),
    .OutW(MsgWidth)
  ) u_prefix_slicer (
    .sel_i  (prefix_index),
    .data_i (prefix),
    .data_o (prefix_sliced)
  );

  if (EnMasking) begin : gen_prefix_masked
    // If Masking is enabled, prefix is two share.
    assign prefix_data[0] = '0;
    assign prefix_data[1] = prefix_sliced;
  end else begin : gen_prefix_unmasked
    // If Unmasked, only one share exists.
    assign prefix_data[0] = prefix_sliced;
  end

  // ==========================================================================
  // function_pad is the unique value padded at the end of the message based on
  // the function among SHA3, SHAKE, cSHAKE. The standard mentioned that SHA3
  // pads `01` , SHAKE pads `1111`, and cSHAKE pads `00`.
  //
  // Then pad10*1() function follows. It adds `1` first then fill 0 until it
  // reaches the block size -1, then adds `1`.
  //
  // It means always `1` is followed by the function pad.
  logic [4:0] funcpad;

  logic [MsgWidth-1:0] funcpad_data [Share];

  always_comb begin
    unique case (mode_i)
      Sha3:   funcpad = 5'b 00110;
      Shake:  funcpad = 5'b 11111;
      CShake: funcpad = 5'b 00100;

      default: begin
        // Just create non-padding but pad10*1 only
        funcpad = 5'b 00001;
      end
    endcase
  end

  // ==========================================================================
  // `zero_with_endbit` contains all zero unless the message is for the last
  // MsgWidth beat in the block. If it is the end of the block, the last bit
  // will be set to complete pad10*1() functionality.
  logic [MsgWidth-1:0] zero_with_endbit [Share];

  if (EnMasking) begin : gen_zeroend_masked
    assign zero_with_endbit[0]               = '0;
    assign zero_with_endbit[1][MsgWidth-1]   = end_of_block;
    assign zero_with_endbit[1][MsgWidth-2:0] = '0;
  end else begin : gen_zeroend_unmasked
    assign zero_with_endbit[0][MsgWidth-1]   = end_of_block;
    assign zero_with_endbit[0][MsgWidth-2:0] = '0;
  end

  // ==========================================================================
  // Data mux for output data

  assign keccak_addr_o = (sent_message < block_addr_limit) ? sent_message : '0;

  always_comb begin
    unique case (sel_mux)
      MuxFifo:    keccak_data_o = msg_data_i;
      MuxPrefix:  keccak_data_o = prefix_data;
      MuxFuncPad: keccak_data_o = funcpad_data;
      MuxZeroEnd: keccak_data_o = zero_with_endbit;

      // MuxNone
      default:  keccak_data_o = '{default:'0};
    endcase
  end

  always_comb begin
    unique case (sel_mux)
      MuxFifo:    keccak_valid_o = msg_valid_i & ~hold_msg & ~en_msgbuf;
      MuxPrefix:  keccak_valid_o = fsm_keccak_valid;
      MuxFuncPad: keccak_valid_o = fsm_keccak_valid;
      MuxZeroEnd: keccak_valid_o = fsm_keccak_valid;

      // MuxNone
      default:  keccak_valid_o = 1'b 0;
    endcase
  end

  always_comb begin
    unique case (sel_mux)
      MuxFifo:    msg_ready_o = en_msgbuf | (keccak_ready_i & ~hold_msg);
      MuxPrefix:  msg_ready_o = 1'b 0;
      MuxFuncPad: msg_ready_o = 1'b 0;
      MuxZeroEnd: msg_ready_o = 1'b 0;

      // MuxNone
      default: msg_ready_o = 1'b 0;
    endcase
  end

  // prim_packer : packing to 64bit to update keccak storage
  // two prim_packer in this module are used to pack the data received from
  // upper layer (KMAC core) and also the 5bit padding bits.
  // It is assumed that the message from upper layer could be partial at the
  // end of the message. Then the 2 or 4bit padding is required. It can be
  // handled by some custom logic or could be done by prim_packer.
  // If packer is used, the MSG_FIFO doesn't have to have another prim_packer
  // in front of the FIFO. This logic can handle the partial writes from the
  // software.
  //
  // If a custom logic is implemented here, prim_packer is necessary in front
  // of the FIFO, as this logic only appends at the end of the message when
  // `process_i` is asserted. Also, in this case, even prim_packer is not
  // needed, still 64bit registers to latch the partial write is required.
  // If not, the logic has to delay the acceptance of the incoming write
  // accesses. It may trigger the back-pressuring in some case which may result
  // that the software(or upper layer) may not set process_i.
  //
  // For custom logic, it could be implemented by the 8 mux selection.
  // for instance: (subject to be changed)
  //   unique case (sent_byte[2:0]) // generated from msg_strb_i
  //     3'b 000: funcpad_merged = {end_of_block, 63'(function_pad)                  };
  //     3'b 001: funcpad_merged = {end_of_block, 55'(function_pad), msg_data_i[ 7:0]};
  //     3'b 010: funcpad_merged = {end_of_block, 47'(function_pad), msg_data_i[15:0]};
  //     3'b 011: funcpad_merged = {end_of_block, 39'(function_pad), msg_data_i[23:0]};
  //     3'b 100: funcpad_merged = {end_of_block, 31'(function_pad), msg_data_i[31:0]};
  //     3'b 101: funcpad_merged = {end_of_block, 23'(function_pad), msg_data_i[39:0]};
  //     3'b 110: funcpad_merged = {end_of_block, 15'(function_pad), msg_data_i[47:0]};
  //     3'b 111: funcpad_merged = {end_of_block,  7'(function_pad), msg_data_i[55:0]};
  //     default: funcpad_merged = '0;
  //   endcase

  // internal buffer to store partial write. It doesn't have to store last byte as it
  // stores only when partial write.
  logic [MsgWidth-8-1:0] msg_buf [Share];
  logic [MsgStrbW-1-1:0] msg_strb;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      msg_buf  <= '{default:'0};
      msg_strb <= '0;
    end else if (en_msgbuf) begin
      for (int i = 0 ; i < Share ; i++) begin
        msg_buf[i]  <= msg_data_i[i][0+:(MsgWidth-8)];
      end
      msg_strb <= msg_strb_i[0+:(MsgStrbW-1)];
    end else if (clr_msgbuf) begin
      msg_buf  <= '{default:'0};
      msg_strb <= '0;
    end
  end

  if (EnMasking) begin : gen_funcpad_data_masked
    always_comb begin
      unique case (msg_strb)
        7'b 000_0000: begin
          funcpad_data[0] = '0;
          funcpad_data[1] = {end_of_block, 63'(funcpad)                  };
        end
        7'b 000_0001: begin
          funcpad_data[0] = {56'h0,                      msg_buf[0][ 7:0]};
          funcpad_data[1] = {end_of_block, 55'(funcpad), msg_buf[1][ 7:0]};
        end
        7'b 000_0011: begin
          funcpad_data[0] = {48'h0,                      msg_buf[0][15:0]};
          funcpad_data[1] = {end_of_block, 47'(funcpad), msg_buf[1][15:0]};
        end
        7'b 000_0111: begin
          funcpad_data[0] = {40'h0,                      msg_buf[0][23:0]};
          funcpad_data[1] = {end_of_block, 39'(funcpad), msg_buf[1][23:0]};
        end
        7'b 000_1111: begin
          funcpad_data[0] = {32'h0,                      msg_buf[0][31:0]};
          funcpad_data[1] = {end_of_block, 31'(funcpad), msg_buf[1][31:0]};
        end
        7'b 001_1111: begin
          funcpad_data[0] = {24'h0,                      msg_buf[0][39:0]};
          funcpad_data[1] = {end_of_block, 23'(funcpad), msg_buf[1][39:0]};
        end
        7'b 011_1111: begin
          funcpad_data[0] = {16'h0,                      msg_buf[0][47:0]};
          funcpad_data[1] = {end_of_block, 15'(funcpad), msg_buf[1][47:0]};
        end
        7'b 111_1111: begin
          funcpad_data[0] = { 8'h0,                      msg_buf[0][55:0]};
          funcpad_data[1] = {end_of_block,  7'(funcpad), msg_buf[1][55:0]};
        end

        default: funcpad_data = '{default:'0};
      endcase
    end
  end else begin : gen_funcpad_data_unmasked
    always_comb begin
      unique case (msg_strb)
        7'b 000_0000: funcpad_data[0] = {end_of_block, 63'(funcpad)                  };
        7'b 000_0001: funcpad_data[0] = {end_of_block, 55'(funcpad), msg_buf[0][ 7:0]};
        7'b 000_0011: funcpad_data[0] = {end_of_block, 47'(funcpad), msg_buf[0][15:0]};
        7'b 000_0111: funcpad_data[0] = {end_of_block, 39'(funcpad), msg_buf[0][23:0]};
        7'b 000_1111: funcpad_data[0] = {end_of_block, 31'(funcpad), msg_buf[0][31:0]};
        7'b 001_1111: funcpad_data[0] = {end_of_block, 23'(funcpad), msg_buf[0][39:0]};
        7'b 011_1111: funcpad_data[0] = {end_of_block, 15'(funcpad), msg_buf[0][47:0]};
        7'b 111_1111: funcpad_data[0] = {end_of_block,  7'(funcpad), msg_buf[0][55:0]};

        default: funcpad_data = '{default:'0};
      endcase
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // Prefix size is smaller than the smallest Keccak Block Size, which is 72 bytes.
  `ASSERT_INIT(PrefixLessThanBlock_A, PrefixSize/8 < KeccakRate[4])

  // Some part of datapath in sha3pad assumes Data width as 64bit.
  // If data width need to be changed, funcpad_data part should be changed too.
  // Also, The blocksize shall be divided by MsgWidth, which means, MsgWidth
  // can be {16, 32, 64} even funcpad_data mux is fully flexible.
  `ASSERT_INIT(MsgWidthidth_A, MsgWidth == 64)

  // Assume pulse signals: start, process, done
  `ASSUME(StartPulse_A, start_i |=> !start_i)
  `ASSUME(ProcessPulse_A, process_i |=> !process_i)
  `ASSUME(DonePulse_A,
    prim_mubi_pkg::mubi4_test_true_strict(done_i) |=>
      prim_mubi_pkg::mubi4_test_false_strict(done_i))

  // ASSERT output pulse signals: absorbed_o, keccak_run_o
  `ASSERT(AbsorbedPulse_A,
    prim_mubi_pkg::mubi4_test_true_strict(absorbed_o) |=>
      prim_mubi_pkg::mubi4_test_false_strict(absorbed_o))
  `ASSERT(KeccakRunPulse_A, keccak_run_o |=> !keccak_run_o)

  // start_i, done_i, process_i cannot set high at the same time
  `ASSUME(StartProcessDoneMutex_a,
    $onehot0({
      start_i,
      process_i,
      prim_mubi_pkg::mubi4_test_true_loose(done_i)
    }))

  // Sequence, start_i --> process_i --> absorbed_o --> done_i
  //`ASSUME(Sequence_a, start_i ##[1:$] process_i ##[1:$] ##[1:$] absorbed_o ##[1:$] done_i)

`ifndef SYNTHESIS
  // Process only asserts after start and all message are fed.
  // These valid signals are qualifier of FPV to trigger the control signal
  // It is a little bit hard to specify these criteria in SVA property so creating
  // qualifiers in RTL form is easier.
  logic start_valid, process_valid, absorb_valid, done_valid;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      start_valid <= 1'b 1;
    end else if (start_i) begin
      start_valid <= 1'b 0;
    end else if (prim_mubi_pkg::mubi4_test_true_strict(done_i)) begin
      start_valid <= 1'b 1;
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      process_valid <= 1'b 0;
    end else if (start_i) begin
      process_valid <= 1'b 1;
    end else if (process_i) begin
      process_valid <= 1'b 0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      done_valid <= 1'b 0;
    end else if (prim_mubi_pkg::mubi4_test_true_strict(absorbed_o)) begin
      done_valid <= 1'b 1;
    end else if (prim_mubi_pkg::mubi4_test_true_strict(done_i)) begin
      done_valid <= 1'b 0;
    end
  end

  // Message can be fed in between start_i and process_i.
  `ASSUME(MessageCondition_M, msg_valid_i && msg_ready_o |-> process_valid && !process_i)

  // Message ready should be asserted only in between start_i and process_i
  `ASSERT(MsgReadyCondition_A, msg_ready_o |-> process_valid && !process_i)

  `ASSUME(ProcessCondition_M, process_i |-> process_valid)
  `ASSUME(StartCondition_M, start_i |-> start_valid)
  `ASSUME(DoneCondition_M,
    prim_mubi_pkg::mubi4_test_true_strict(done_i) |-> done_valid)

  // Assume mode_i and strength_i are stable during the operation
  // This will be guarded at the kmac top level
  `ASSUME(ModeStableDuringOp_M,
    $changed(mode_i) |-> start_valid)
  `ASSUME(StrengthStableDuringOp_M,
    $changed(strength_i) |-> start_valid)

`endif // SYNTHESIS

  // If not full block is written, the pad shall send message to keccak_round
  // If it is end of the message, the state moves to StPad and send the request
  `ASSERT(CompleteBlockWhenProcess_A,
    $rose(process_latched) && (!end_of_block && !sent_blocksize )
    && !(st inside {StPrefixWait, StMessageWait}) |-> ##[1:5] keccak_valid_o,
    clk_i, !rst_ni || lc_escalate_en_i != lc_ctrl_pkg::Off)

  // If process_i asserted, completion shall be asserted shall be asserted
  //`ASSERT(ProcessToAbsorbed_A, process_i |=> strong(##[24*Share:$] absorbed_o))


  // Assumption of input mode_i and strength_i
  // SHA3 variants: SHA3-224, SHA3-256, SHA3-384, SHA3-512
  // SHAKE, cSHAKE variants: SHAKE128, SHAKE256, cSHAKE128, cSHAKE256
  `ASSUME_FPV(ModeStrengthCombinations_M,
    start_i |->
      (mode_i == Sha3 && (strength_i inside {L224, L256, L384, L512})) ||
      ((mode_i == Shake || mode_i == CShake) && (strength_i inside {L128, L256})),
    clk_i, !rst_ni)

  // No partial write is allowed for Message FIFO interface
  `ASSUME(NoPartialMsgFifo_M,
    keccak_valid_o && (sel_mux == MuxFifo) |-> (&msg_strb_i) == 1'b1,
    clk_i, !rst_ni)

  // When transaction is stored into msg_buf, it shall be partial write.
  `ASSUME(AlwaysPartialMsgBuf_M,
    en_msgbuf |-> msg_valid_i && (msg_strb_i[MsgStrbW-1] == 1'b0),
    clk_i, !rst_ni)

  // if partial write comes and is acked, then no more msg_valid_i until
  // next message
  `ASSUME(PartialEndOfMsg_M,
    msg_valid_i && msg_ready_o && msg_partial |=>
      !msg_valid_i ##[1:$] $stable(msg_valid_i) ##1 process_latched,
    clk_i, !rst_ni)

  // At the first clock in StPad01 state, sent_blocksize shall not be set
  `ASSERT(Pad01NotAttheEndOfBlock_A,
    (st == StPad && st_d == StPad01) |-> !end_of_block,
    clk_i, !rst_ni)

  // When data sent to the keccak_round, the address should be in the range
  `ASSERT(KeccakAddrInRange_A,
    keccak_valid_o |-> keccak_addr_o < KeccakRate[strength_i],
    clk_i, !rst_ni)

  // NS data shall be stable during the operation.
  //`ASSUME(NsStableInProcess_A,
  //  $stable(ns_data_i) throughout(start_i ##[1:$] process_i ##[1:$] absorbed_o),
  //  clk_i, !rst_ni)

  // Functional Coverage
  `COVER(StMessageFeed_C, st == StMessage)
  `COVER(StPad_C, st == StPad01 && sent_blocksize)
  `COVER(StPadSendMsg_C, st == StPad01 && keccak_ack)
  `COVER(StComplete_C, st == StPadFlush)
endmodule
