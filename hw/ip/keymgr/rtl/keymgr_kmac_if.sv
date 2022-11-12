// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager interface to kmac
//

`include "prim_assert.sv"

module keymgr_kmac_if import keymgr_pkg::*;(
  input clk_i,
  input rst_ni,

  // data input interfaces
  input [AdvDataWidth-1:0] adv_data_i,
  input [IdDataWidth-1:0] id_data_i,
  input [GenDataWidth-1:0] gen_data_i,
  input [3:0] inputs_invalid_i,
  output logic inputs_invalid_o,

  // keymgr control to select appropriate inputs
  input adv_en_i,
  input id_en_i,
  input gen_en_i,
  output logic done_o,
  output logic [Shares-1:0][kmac_pkg::AppDigestW-1:0] data_o,

  // actual connection to kmac
  output kmac_pkg::app_req_t kmac_data_o,
  input  kmac_pkg::app_rsp_t kmac_data_i,

  // entropy input
  output logic prng_en_o,
  input [Shares-1:0][RandWidth-1:0] entropy_i,

  // error outputs
  output logic fsm_error_o,
  output logic kmac_error_o,
  output logic kmac_done_error_o,
  output logic cmd_error_o
);


  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 6 -n 10 \
  //      -s 2292624416 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (46.67%)
  //  6: ||||||||||||||||| (40.00%)
  //  7: ||||| (13.33%)
  //  8: --
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 9
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    StIdle    = 10'b1110100010,
    StTx      = 10'b0010011011,
    StTxLast  = 10'b0101000000,
    StOpWait  = 10'b1000101001,
    StClean   = 10'b1111111101,
    StError   = 10'b0011101110
  } data_state_e;

  localparam int AdvRem = AdvDataWidth % KmacDataIfWidth;
  localparam int IdRem  = IdDataWidth  % KmacDataIfWidth;
  localparam int GenRem = GenDataWidth % KmacDataIfWidth;

  // the remainder must be in number of bytes
  `ASSERT_INIT(AdvRemBytes_A, AdvRem % 8 == 0)
  `ASSERT_INIT(IdRemBytes_A,  IdRem  % 8 == 0)
  `ASSERT_INIT(GenRemBytes_A, GenRem % 8 == 0)

  // Number of kmac transactions required
  localparam int AdvRounds = (AdvDataWidth + KmacDataIfWidth - 1) / KmacDataIfWidth;
  localparam int IdRounds  = (IdDataWidth + KmacDataIfWidth - 1) / KmacDataIfWidth;
  localparam int GenRounds = (GenDataWidth + KmacDataIfWidth - 1) / KmacDataIfWidth;
  localparam int MaxRounds = KDFMaxWidth  / KmacDataIfWidth;

  // calculated parameters for number of roudns and interface width
  localparam int CntWidth = $clog2(MaxRounds);
  localparam int IfBytes = KmacDataIfWidth / 8;
  localparam int DecoyCopies = KmacDataIfWidth / RandWidth;
  localparam int DecoyOutputCopies = (kmac_pkg::AppDigestW / RandWidth) * Shares;

  localparam int unsigned LastAdvRoundInt = AdvRounds - 1;
  localparam int unsigned LastIdRoundInt = IdRounds - 1;
  localparam int unsigned LastGenRoundInt = GenRounds - 1;
  localparam bit [CntWidth-1:0] LastAdvRound = LastAdvRoundInt[CntWidth-1:0];
  localparam bit [CntWidth-1:0] LastIdRound = LastIdRoundInt[CntWidth-1:0];
  localparam bit [CntWidth-1:0] LastGenRound = LastGenRoundInt[CntWidth-1:0];

  // byte mask for the last transfer
  localparam logic [IfBytes-1:0] AdvByteMask = (AdvRem > 0) ? (2**(AdvRem/8)-1) : {IfBytes{1'b1}};
  localparam logic [IfBytes-1:0] IdByteMask  = (IdRem > 0)  ? (2**(IdRem/8)-1)  : {IfBytes{1'b1}};
  localparam logic [IfBytes-1:0] GenByteMask = (GenRem > 0) ? (2**(GenRem/8)-1) : {IfBytes{1'b1}};

  logic [MaxRounds-1:0][KmacDataIfWidth-1:0] adv_data;
  logic [MaxRounds-1:0][KmacDataIfWidth-1:0] id_data;
  logic [MaxRounds-1:0][KmacDataIfWidth-1:0] gen_data;
  logic [CntWidth-1:0] cnt;
  logic [CntWidth-1:0] rounds;
  logic [KmacDataIfWidth-1:0] decoy_data;
  logic valid;
  logic last;
  logic [IfBytes-1:0] strb;
  logic cnt_clr, cnt_set, cnt_en;
  logic start;
  logic [3:0] inputs_invalid_d, inputs_invalid_q;
  logic clr_err;
  logic kmac_done_vld;
  logic cmd_chk;

  data_state_e state_q, state_d;

  // 0 pad to the appropriate width
  // this is basically for scenarios where *DataWidth % KmacDataIfWidth != 0
  assign adv_data = KDFMaxWidth'(adv_data_i);
  assign id_data  = KDFMaxWidth'(id_data_i);
  assign gen_data = KDFMaxWidth'(gen_data_i);

  assign start = adv_en_i | id_en_i | gen_en_i;

  logic cnt_err;
  // SEC_CM: KMAC_IF.CTR.REDUN
  prim_count #(
    .Width(CntWidth),
    .ResetValue({CntWidth{1'b1}})
  ) u_cnt (
    .clk_i,
    .rst_ni,
    .clr_i(cnt_clr),
    .set_i(cnt_set),
    .set_cnt_i(rounds),
    .incr_en_i(1'b0),
    .decr_en_i(cnt_en),
    .step_i(CntWidth'(1'b1)),
    .cnt_o(cnt),
    .cnt_next_o(),
    .err_o(cnt_err)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      inputs_invalid_q <= '0;
    end else begin
      inputs_invalid_q <= inputs_invalid_d;
    end
   end

  // SEC_CM: KMAC_IF.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, data_state_e, StIdle)

  always_comb begin
    cnt_clr = 1'b0;
    cnt_set = 1'b0;
    cnt_en  = 1'b0;
    valid   = 1'b0;
    last    = 1'b0;
    strb    = '0;
    done_o  = 1'b0;
    state_d = state_q;
    rounds  = '0;

    clr_err = '0;
    fsm_error_o = '0;
    kmac_error_o = '0;

    kmac_done_vld = '0;

    cmd_chk = 1'b1;

    unique case (state_q)

      StIdle: begin
        // if for some reason multiple bits are set, adv_en has priority
        // as the current key state will be destroyed

        // cross check for commands once transaction begins
        cmd_chk = '0;
        if (start) begin
          cnt_set = 1'b1;
          if (adv_en_i) begin
            rounds = LastAdvRound;
          end else if (id_en_i) begin
            rounds = LastIdRound;
          end else if (gen_en_i) begin
            rounds = LastGenRound;
          end
          // in case we are sending only 1 entry
          state_d = (rounds == 0) ? StTxLast : StTx;
        end
      end

      StTx: begin
        valid = 1'b1;
        strb = {IfBytes{1'b1}};

        // transaction accepted
        if (kmac_data_i.ready) begin
          cnt_en = 1'b1;

          // second to last beat
          if (cnt == CntWidth'(1'b1)) begin
            state_d = StTxLast;
          end
        end

      end

      StTxLast: begin
        valid = 1'b1;
        last = 1'b1;

        if (adv_en_i) begin
          strb = AdvByteMask;
        end else if (id_en_i) begin
          strb = IdByteMask;
        end else if (gen_en_i) begin
          strb = GenByteMask;
        end

        // transaction accepted
        cnt_clr = kmac_data_i.ready;
        state_d = kmac_data_i.ready ? StOpWait : StTxLast;

      end

      StOpWait: begin
        kmac_done_vld = 1'b1;
        if (kmac_data_i.done) begin
          kmac_error_o = kmac_data_i.error;
          done_o = 1'b1;
          state_d = StClean;
        end
      end

      StClean: begin
        cmd_chk = '0;
        done_o = 1'b1;

        // wait for control side to ack done by waiting start de-assertion
        if (!start) begin
          done_o = 1'b0;
          clr_err = 1'b1;
          state_d = StIdle;
        end
      end

      // trigger error
      default: begin
        // This state is terminal
        done_o = 1'b1;
        fsm_error_o = 1'b1;
      end

    endcase // unique case (state_q)

    // unconditional error transitions
    // counter errors may disturb the fsm flow and are
    // treated like fsm errors
    if (cnt_err) begin
      state_d = StError;
      fsm_error_o = 1;
      done_o = 1'b1;
    end
  end

  // when transaction is not complete, populate the data with random
  assign data_o = start && done_o ?
                  {kmac_data_i.digest_share1,
                   kmac_data_i.digest_share0} :
                  {DecoyOutputCopies{entropy_i[0]}};

  // The input invalid check is done whenever transactions are ongoing with kmac
  // once set, it cannot be unset until transactions are fully complete
  always_comb begin
    inputs_invalid_d = inputs_invalid_q;

    if (clr_err) begin
      inputs_invalid_d = '0;
    end else if (valid) begin
      inputs_invalid_d[OpAdvance]  = adv_en_i & (inputs_invalid_i[OpAdvance] |
                                                 inputs_invalid_q[OpAdvance]);
      inputs_invalid_d[OpGenId]    = id_en_i  & (inputs_invalid_i[OpGenId]   |
                                                 inputs_invalid_q[OpGenId]);
      inputs_invalid_d[OpGenSwOut] = gen_en_i & (inputs_invalid_i[OpGenSwOut]|
                                                 inputs_invalid_q[OpGenSwOut]);
      inputs_invalid_d[OpGenHwOut] = gen_en_i & (inputs_invalid_i[OpGenHwOut]|
                                                 inputs_invalid_q[OpGenHwOut]);
    end
  end

  // immediately assert errors
  assign inputs_invalid_o = |inputs_invalid_d;

  logic [CntWidth-1:0] adv_sel, id_sel, gen_sel;
  assign adv_sel = LastAdvRound - cnt;
  assign id_sel = LastIdRound - cnt;
  assign gen_sel = LastGenRound - cnt;

  // The count is maintained as a downcount
  // so a subtract is necessary to send the right byte
  // alternatively we can also reverse the order of the input
  assign decoy_data = {DecoyCopies{entropy_i[1]}};
  always_comb begin
    kmac_data_o.data  = decoy_data;
    if (|cmd_error_o || inputs_invalid_o || fsm_error_o) begin
      kmac_data_o.data  = decoy_data;
    end else if (valid && adv_en_i) begin
      kmac_data_o.data  = adv_data[adv_sel];
    end else if (valid && id_en_i) begin
      kmac_data_o.data  = id_data[id_sel];
    end else if (valid && gen_en_i) begin
      kmac_data_o.data  = gen_data[gen_sel];
    end
  end

  assign kmac_data_o.valid = valid;
  assign kmac_data_o.last  = last;
  assign kmac_data_o.strb  = strb;

  // kmac done is asserted outside of expected window
  // SEC_CM: KMAC_IF_DONE.CTRL.CONSISTENCY
  logic kmac_done_err_q, kmac_done_err_d;
  assign kmac_done_err_d = ~kmac_done_vld & kmac_data_i.done |
                           kmac_done_err_q;
  assign kmac_done_error_o = kmac_done_err_q;


  // the enables must be 1 hot
  logic [2:0] enables_d, enables_q, enables_sub;
  assign enables_d = {adv_en_i, id_en_i, gen_en_i};
  assign enables_sub = enables_d - 1'b1;

  // cross check to ensure the one-hot command that kicked off
  // the transaction remains consistent throughout.
  logic cmd_consty_err_q, cmd_consty_err_d;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      enables_q <= '0;
    end else if (cnt_set) begin
      enables_q <= enables_d;
    end
  end
  assign cmd_consty_err_d = (cmd_chk & (enables_q != enables_d)) |
                            cmd_consty_err_q;

  // if a one hot error occurs, latch onto it permanently
  // SEC_CM: KMAC_IF_CMD.CTRL.CONSISTENCY
  logic one_hot_err_q, one_hot_err_d;
  assign one_hot_err_d = |(enables_d & enables_sub) |
                         one_hot_err_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      one_hot_err_q <= '0;
      kmac_done_err_q <= '0;
      cmd_consty_err_q <= '0;
    end else begin
      one_hot_err_q <= one_hot_err_d;
      kmac_done_err_q <= kmac_done_err_d;
      cmd_consty_err_q <= cmd_consty_err_d;
    end
  end

  // command error occurs if kmac errors or if the command itself is invalid
  assign cmd_error_o = one_hot_err_q | cmd_consty_err_q;

  // request entropy to churn whenever a transaction is accepted
  assign prng_en_o = kmac_data_o.valid & kmac_data_i.ready;

  // as long as we are transmitting, the strobe should never be 0.
  `ASSERT(LastStrb_A, valid |-> strb != '0)


endmodule // keymgr_kmac_if
