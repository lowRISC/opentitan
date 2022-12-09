// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Phy Prog Module
//
// This module implements the flash phy program operation
//
// The flash phy prog module is mainly responsible for packing incoming data
// transactions into appropriate flash word sizes.
//
// This is done primarily for two reasons
// - Reduce program stress on the flash
//   Flash modules usually have a limit to how many times adjacent words can be programmed.
//   If a programming beat is longer than a flash word, it would be best to compact those
//   beats into multiples of the flash word size to improve performance and reduce
//   unecessary programmings
//
// - Observe minimum block cipher sizes for scrambling / descrambling and ECC.
//   Scrambling algorithms and ECC work on a specific chunk of data.  When these features
//   are enabled, the phy controller needs to ensure there is enough data to satisfy that
//   request.

module flash_phy_prog import flash_phy_pkg::*; (
  input clk_i,
  input rst_ni,
  input prim_mubi_pkg::mubi4_t disable_i,
  input req_i,
  input scramble_i,
  input ecc_i,
  input [WordSelW-1:0] sel_i,
  input [BusFullWidth-1:0] data_i,
  input last_i,
  input ack_i,  // ack means request has been accepted by flash
  input done_i, // done means requested transaction has completed
  input calc_ack_i,
  input scramble_ack_i,
  input [DataWidth-1:0] mask_i,
  input [DataWidth-1:0] scrambled_data_i,
  output logic calc_req_o,
  output logic scramble_req_o,
  output logic req_o,
  output logic last_o, // last beat of an incoming transaction
  output logic ack_o,
  // block data does not contain ecc / metadata portion
  output logic [DataWidth-1:0] block_data_o,
  output logic [FullDataWidth-1:0] data_o,
  output logic fsm_err_o,
  output logic intg_err_o
);

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 11 -n 11 \
  //      -s 2968771430 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (40.00%)
  //  6: ||||||||||||||||| (34.55%)
  //  7: |||||| (12.73%)
  //  8: ||||| (10.91%)
  //  9:  (1.82%)
  // 10: --
  // 11: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 9
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 8
  //
  localparam int StateWidth = 11;
  typedef enum logic [StateWidth-1:0] {
    StIdle          = 11'b11111111110,
    StPrePack       = 11'b00001110111,
    StPackData      = 11'b10100100011,
    StPostPack      = 11'b11010000101,
    StCalcPlainEcc  = 11'b01101011011,
    StReqFlash      = 11'b01010110010,
    StWaitFlash     = 11'b00100111000,
    StCalcMask      = 11'b00000001110,
    StScrambleData  = 11'b00011101001,
    StCalcEcc       = 11'b00111010100,
    StDisabled      = 11'b10001000000
  } state_e;
  state_e state_d, state_q;

  typedef enum logic [1:0] {
    Filler,
    Actual
  } data_sel_e;

  // The currently observed data beat
  logic [WordSelW-1:0] idx;
  logic [WordSelW-1:0] idx_sub_one;
  logic pack_valid;
  logic [BusWidth-1:0] pack_data;
  logic align_next;
  data_sel_e data_sel;

  localparam int MaxIdx = WidthMultiple - 1;

  logic [WidthMultiple-1:0][BusWidth-1:0] packed_data;
  logic plain_ecc_en;

  // selects empty data or real data
  assign pack_data  = (data_sel == Actual) ? data_i[BusWidth-1:0] : {BusWidth{1'b1}};

  logic data_intg_ok;
  logic data_err;

  // use the tlul integrity module directly for bus integrity
  // SEC_CM: MEM.BUS.INTEGRITY
  tlul_data_integ_dec u_data_intg_chk (
    .data_intg_i(data_i),
    .data_err_o(data_err)
  );
  assign data_intg_ok = ~data_err;

  logic data_invalid_q, data_invalid_d;
  // hold on integrity failure indication until reset
  assign data_invalid_d = data_invalid_q |
                          (pack_valid & ~data_intg_ok);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_invalid_q <= '0;
    end else begin
      data_invalid_q <= data_invalid_d;
    end
  end

  // indication to upper layer prescence of error
  assign intg_err_o = data_invalid_q;

  // if integrity failure is seen, fake communication with flash
  // and simply terminate
  logic ack, done;
  assign ack = ack_i | data_invalid_q;
  assign done = done_i | data_invalid_q;

  // next idx will be aligned
  assign idx_sub_one = idx - 1'b1;
  assign align_next = (idx > '0) ? (idx_sub_one == sel_i) : 1'b0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      idx <= '0;
    end else if (pack_valid && idx == MaxIdx) begin
      // when a flash word is packed full, return index to 0
      idx <= '0;
    end else if (pack_valid) begin
      // increment otherwise
      idx <= idx + 1'b1;
    end
  end


  // SEC_CM: PHY_PROG.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StIdle)

  // If the first beat of an incoming transaction is not aligned to word boundary (for example
  // if each flash word is 4 bus words wide, and the first word to program starts at index 1),
  // the fsm pre-packs the flash word with empty words until the supplied index.
  // Once at the index, real data supplied from the flash controller is packed until the last
  // beat of data.  At the last beat of data, if it is not also aligned (index 3 in this example),
  // more empty words are packed at the end to fill out the word.
  //
  always_comb begin
    state_d = state_q;

    pack_valid = 1'b0;
    data_sel = Filler;
    plain_ecc_en = 1'b0;
    req_o = 1'b0;
    ack_o = 1'b0;
    last_o = 1'b0;
    calc_req_o = 1'b0;
    scramble_req_o = 1'b0;
    fsm_err_o = 1'b0;

    unique case (state_q)
      StIdle: begin
        // if first beat of a transaction is not aligned, prepack with empty bits
        if (prim_mubi_pkg::mubi4_test_true_loose(disable_i)) begin
          // only disable during idle state to ensure program is able to gracefully complete
          // this is important as we do not want to accidentally disturb any electrical procedure
          // internal to the flash macro
          state_d = StDisabled;
        end else if (req_i && |sel_i) begin
          state_d = StPrePack;
        end else if (req_i) begin
          state_d = StPackData;
        end
      end

      StPrePack: begin
        // pack until currently supplied data
        pack_valid = (idx < sel_i);
        if (idx == align_next) begin
          state_d = StPackData;
        end
      end

      StPackData: begin
        pack_valid = req_i;
        data_sel = Actual;

        if (req_i && idx == MaxIdx) begin
          // last beat of a flash word
          state_d = StCalcPlainEcc;
        end else if (req_i && last_i) begin
          // last beat is not aligned with the last entry of flash word
          state_d = StPostPack;
        end else if (req_i) begin
          ack_o = 1'b1;
        end
      end

      StPostPack: begin
        // supply filler data
        pack_valid = 1'b1;
        data_sel = Filler;

        // finish packing remaining entries
        if (idx == MaxIdx) begin
          state_d = StCalcPlainEcc;
        end
      end

      StCalcPlainEcc: begin
        plain_ecc_en = 1'b1;
        state_d = scramble_i ? StCalcMask : StReqFlash;
      end

      StCalcMask: begin
        calc_req_o = 1'b1;

        if (calc_ack_i) begin
          state_d = StScrambleData;
        end
      end

      StScrambleData: begin
        scramble_req_o = 1'b1;

        if (scramble_ack_i) begin
          state_d = StCalcEcc;
        end
      end

      StCalcEcc: begin
        state_d = StReqFlash;
      end

      StReqFlash: begin
        // only request flash if data integrity was valid
        req_o = ~data_invalid_q;
        last_o = last_i;

        // if this is the last beat of the program burst
        //   - wait for done
        // if this is NOT the last beat
        //   - ack the upstream request and accept more beats
        if (last_i) begin
          state_d = ack ? StWaitFlash : StReqFlash;
        end else begin
          ack_o = ack;
          state_d = ack ? StIdle : StReqFlash;
        end
      end

      StWaitFlash: begin
        if (done) begin
          ack_o = 1'b1;
          state_d = StIdle;
        end
      end

      StDisabled: begin
        state_d = StDisabled;
      end

      default: begin
        fsm_err_o = 1'b1;
      end

    endcase // unique case (state_q)

  end

  logic [DataWidth-1:0] mask_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      packed_data <= '0;
      mask_q <= '0;
    end else if (req_o && ack) begin
      packed_data <= '0;
    end else if (calc_req_o && calc_ack_i) begin
      packed_data <= packed_data ^ mask_i;
      mask_q <= mask_i;
    end else if (scramble_req_o && scramble_ack_i) begin
      packed_data <= scrambled_data_i[DataWidth-1:0] ^ mask_q;
    end else if (pack_valid) begin
      packed_data[idx] <= pack_data;
    end
  end

  assign block_data_o = packed_data;

  // ECC handling
  localparam int PlainDataEccWidth = DataWidth + 8;

  logic [FullDataWidth-1:0] ecc_data;
  logic [PlainDataEccWidth-1:0] plain_data_w_ecc;
  logic [PlainIntgWidth-1:0] plain_data_ecc;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      plain_data_ecc <= '1;
    end else if (plain_ecc_en) begin
      plain_data_ecc <= plain_data_w_ecc[DataWidth +: PlainIntgWidth];
    end
  end

  logic [PlainDataWidth-1:0] ecc_data_in;
  assign ecc_data_in = {plain_data_ecc, packed_data};

  // reliability ECC calculation
  prim_secded_hamming_76_68_enc u_enc (
    .data_i(ecc_data_in),
    .data_o(ecc_data)
  );

  // integrity ECC calculation
  // This instance can technically be merged with the instance above, but is
  // kept separate for the sake of convenience
  // The plain data ecc is calculated continously from packed data (which changes
  // from packed data to masked/scrambled data based on software configuration).
  // The actual plain data ECC is explicitly captured during this process when
  // it is required.
  prim_secded_hamming_72_64_enc u_plain_enc (
    .data_i(packed_data),
    .data_o(plain_data_w_ecc)
  );

  logic unused_data;
  assign unused_data = |plain_data_w_ecc;

  // pad the remaining bits with '1' if ecc is not used.
  assign data_o = ecc_i ? ecc_data : {{EccWidth{1'b1}}, ecc_data_in};

  /////////////////////////////////
  // Assertions
  /////////////////////////////////

`ifdef INC_ASSERT
  logic txn_done;
  logic [15:0] done_cnt_d, done_cnt_q;

  assign txn_done = req_i && ack_o && last_i;
  assign done_cnt_d = txn_done ? '0 : (done ? done_cnt_q + 16'h1 : done_cnt_q);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      done_cnt_q <= '0;
    end else begin
      done_cnt_q <= done_cnt_d;
    end
  end

  // We can only observe one done per transaction.
  `ASSERT(OneDonePerTxn_A,  txn_done |-> done_cnt_d == '0)

`endif

  // Prepack state can only pack up to WidthMultiple - 1
  `ASSERT(PrePackRule_A, state_q == StPrePack && pack_valid |-> idx < MaxIdx)

  // Postpack states should never pack the first index (as it would be aligned in that case)
  `ASSERT(PostPackRule_A, state_q == StPostPack && pack_valid |-> idx != '0)

  // The metadata width must always be greater than the ecc width
  `ASSERT_INIT(WidthCheck_A, MetaDataWidth >= EccWidth)

endmodule // flash_phy_prog
