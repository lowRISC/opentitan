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
  output logic [Shares-1:0][KeyWidth-1:0] data_o,

  // actual connection to kmac
  output kmac_data_req_t kmac_data_o,
  input kmac_data_rsp_t kmac_data_i,

  // entropy input
  output logic prng_en_o,
  input [Shares-1:0][RandWidth-1:0] entropy_i,

  // error outputs
  output logic fsm_error_o,
  output logic kmac_error_o,
  output logic cmd_error_o
);

  // Enumeration for working state
  typedef enum logic [2:0] {
    StIdle   = 0,
    StTx     = 1,
    StTxLast = 2,
    StOpWait = 3,
    StClean  = 4
  } data_state_e;

  localparam int AdvRem = AdvDataWidth % KmacDataIfWidth;
  localparam int IdRem  = IdDataWidth  % KmacDataIfWidth;
  localparam int GenRem = GenDataWidth % KmacDataIfWidth;

  // the remainder must be in number of bytes
  `ASSERT_INIT(AdvRemBytes_A, AdvRem % 8 == 0)
  `ASSERT_INIT(IdRemBytes_A,  IdRem  % 8 == 0)
  `ASSERT_INIT(GenRemBytes_A, GenRem % 8 == 0)

  // Number of kmac transactions required
  localparam int AdvRounds = AdvDataWidth / KmacDataIfWidth + (AdvRem > 0);
  localparam int IdRounds  = IdDataWidth  / KmacDataIfWidth + (IdRem > 0);
  localparam int GenRounds = GenDataWidth / KmacDataIfWidth + (GenRem > 0);
  localparam int MaxRounds = KDFMaxWidth  / KmacDataIfWidth;

  // Total transmitted bits, this is the same as *DataWidth if it all
  // fits into kmac data interface
  localparam int AdvWidth = KmacDataIfWidth * AdvRounds;
  localparam int IdWidth  = KmacDataIfWidth * IdRounds;
  localparam int GenWidth = KmacDataIfWidth * GenRounds;

  // calculated parameters for number of roudns and interface width
  localparam int CntWidth = $clog2(MaxRounds);
  localparam int IfBytes = KmacDataIfWidth / 8;
  localparam int DecoyCopies = KmacDataIfWidth / 32;
  localparam int DecoyOutputCopies = (KeyWidth / 32) * Shares;

  // byte mask for the last transfer
  localparam logic [IfBytes-1:0] AdvByteMask = (AdvRem > 0) ? (2**(AdvRem/8)-1) : {IfBytes{1'b1}};
  localparam logic [IfBytes-1:0] IdByteMask  = (IdRem > 0)  ? (2**(IdRem/8)-1)  : {IfBytes{1'b1}};
  localparam logic [IfBytes-1:0] GenByteMask = (GenRem > 0) ? (2**(GenRem/8)-1) : {IfBytes{1'b1}};

  logic [AdvRounds-1:0][KmacDataIfWidth-1:0] adv_data;
  logic [IdRounds-1:0 ][KmacDataIfWidth-1:0] id_data;
  logic [GenRounds-1:0][KmacDataIfWidth-1:0] gen_data;
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

  data_state_e state_q, state_d;

  // 0 pad to the appropriate width
  // this is basically for scenarios where *DataWidth % KmacDataIfWidth != 0
  assign adv_data = AdvWidth'(adv_data_i);
  assign id_data  = IdWidth'(id_data_i);
  assign gen_data = GenWidth'(gen_data_i);

  assign start = adv_en_i | id_en_i | gen_en_i;

  // downcount
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= '0;
    end else if (cnt_clr) begin
      cnt <= '0;
    end else if (cnt_set) begin
      cnt <= rounds;
    end else if (cnt_en && cnt >'0) begin
      cnt <= cnt - 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      inputs_invalid_q <= '0;
      state_q <= StIdle;
    end else begin
      inputs_invalid_q <= inputs_invalid_d;
      state_q <= state_d;
    end
   end


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

    unique case (state_q)

      StIdle: begin
        // if for some reason multiple bits are set, adv_en has priority
        // as the current key state will be destroyed
        if (start) begin
          cnt_set = 1'b1;
          if (adv_en_i) begin
            rounds = AdvRounds - 1;
          end else if (id_en_i) begin
            rounds = IdRounds - 1;
          end else if (gen_en_i) begin
            rounds = GenRounds - 1;
          end

          // we are sending only 1 entry
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
        if (kmac_data_i.done) begin
          kmac_error_o = kmac_data_i.error;
          done_o = 1'b1;
          state_d = StClean;
        end
      end

      StClean: begin
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
  end

  // If an fsm error is detected, there is no guarantee the transaction can completely gracefully.
  // Allow the transaction to terminate early with random data.
  assign data_o = start && done_o && !fsm_error_o ? {kmac_data_i.digest_share1,
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

  // The count is maintained as a downcount
  // so a subtract is necessary to send the right byte
  // alternatively we can also reverse the order of the input
  assign decoy_data = {DecoyCopies{entropy_i[1]}};
  always_comb begin
    kmac_data_o.data  = decoy_data;
    if (|cmd_error_o || inputs_invalid_o || fsm_error_o) begin
      kmac_data_o.data  = decoy_data;
    end else if (valid && adv_en_i) begin
      kmac_data_o.data  = adv_data[AdvRounds-1-cnt];
    end else if (valid && id_en_i) begin
      kmac_data_o.data  = id_data[IdRounds-1-cnt];
    end else if (valid && gen_en_i) begin
      kmac_data_o.data  = gen_data[GenRounds-1-cnt];
    end
  end

  assign kmac_data_o.valid = valid;
  assign kmac_data_o.last  = last;
  assign kmac_data_o.strb  = strb;

  // the enables must be 1 hot
  logic [2:0] enables, enables_sub;
  assign enables = {adv_en_i, id_en_i, gen_en_i};
  assign enables_sub = enables - 1'b1;
  // command error occurs if kmac errors or if the command itself is invalid
  assign cmd_error_o = |(enables & enables_sub);

  // request entropy to churn whenever a transaction is accepted
  assign prng_en_o = kmac_data_o.valid & kmac_data_i.ready;

endmodule // keymgr_kmac_if
