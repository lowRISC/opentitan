// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// The comparator inside the ROM checker
//
// This module is in charge of comparing the digest that was computed over the ROM data with the
// expected digest stored in the top few words.
//

`include "prim_assert.sv"

module rom_ctrl_compare
  import prim_mubi_pkg::mubi4_t;
#(
  parameter int NumWords = 2
) (
  input logic                        clk_i,
  input logic                        rst_ni,

  input logic                        start_i,
  output logic                       done_o,
  output mubi4_t                     good_o,

  // CSR inputs for DIGEST and EXP_DIGEST. Ordered with word 0 as LSB.
  input logic [NumWords*32-1:0]      digest_i,
  input logic [NumWords*32-1:0]      exp_digest_i,

  // To alert system
  output logic                       alert_o
);

  import prim_util_pkg::vbits;
  import prim_mubi_pkg::mubi4_bool_to_mubi;

  `ASSERT_INIT(NumWordsPositive_A, 0 < NumWords)

  localparam int AW = vbits(NumWords);

  localparam int unsigned LastAddrInt = NumWords - 1;
  localparam bit [AW-1:0] LastAddr    = LastAddrInt[AW-1:0];

  logic          addr_incr;
  logic [AW-1:0] addr_q;

  // This module must wait until triggered by a write to start_i. At that point, it cycles through
  // the words of DIGEST and EXP_DIGEST, comparing them to one another and passing each digest word
  // to the key manager. Finally, it gets to the Done state.
  //
  // States:
  //
  //    Waiting
  //    Checking
  //    Done
  //
  // Encoding generated with:
  // $ util/design/sparse-fsm-encode.py -d 3 -m 3 -n 5 -s 1 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (66.67%)
  //  4: |||||||||| (33.33%)
  //  5: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 3
  //
  // SEC_CM: FSM.SPARSE
  typedef enum logic [4:0] {
    Waiting  = 5'b00100,
    Checking = 5'b10010,
    Done     = 5'b11001
  } state_e;

  state_e state_q, state_d;
  logic   matches_q, matches_d;
  logic   fsm_alert;

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, Waiting)

  always_comb begin
    state_d = state_q;
    fsm_alert = 1'b0;
    unique case (state_q)
      Waiting: begin
        if (start_i) state_d = Checking;
      end
      Checking: begin
        if (addr_q == LastAddr) state_d = Done;
      end
      Done: begin
        // Final state
      end
      default: fsm_alert = 1'b1;
    endcase
  end

  // start_i should only be signalled when we're in the Waiting state
  //
  // SEC_CM: COMPARE.CTRL_FLOW.CONSISTENCY
  logic start_alert;
  assign start_alert = start_i && (state_q != Waiting);

  // addr_q should be zero when we're in the Waiting state
  //
  // SEC_CM: COMPARE.CTR.CONSISTENCY
  logic wait_addr_alert;
  assign wait_addr_alert = (state_q == Waiting) && (addr_q != '0);

  // addr_q should be LastAddr when we're in the Done state
  //
  // SEC_CM: COMPARE.CTR.CONSISTENCY
  logic done_addr_alert;
  assign done_addr_alert = (state_q == Done) && (addr_q != LastAddr);

  // Increment addr_q on each cycle except the last when in Checking. The prim_count primitive
  // doesn't overflow but in case NumWords is not a power of 2, we need to take care of this
  // ourselves.
  assign addr_incr = (state_q == Checking) && (addr_q != LastAddr);

  // SEC_CM: COMPARE.CTR.REDUN
  logic addr_ctr_alert;
  prim_count #(
    .Width(AW)
  ) u_prim_count_addr (
    .clk_i,
    .rst_ni,
    .clr_i(1'b0),
    .set_i(1'b0),
    .set_cnt_i('0),
    .incr_en_i(addr_incr),
    .decr_en_i(1'b0),
    .step_i(AW'(1)),
    .cnt_o(addr_q),
    .cnt_next_o(),
    .err_o(addr_ctr_alert)
  );

  logic [AW+5-1:0] digest_idx;
  logic [31:0]     digest_word, exp_digest_word;
  assign digest_idx = {addr_q, 5'd31};
  assign digest_word = digest_i[digest_idx -: 32];
  assign exp_digest_word = exp_digest_i[digest_idx -: 32];

  assign matches_d = matches_q && (digest_word == exp_digest_word);
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      matches_q <= 1'b1;
    end else begin
      if (state_q == Checking) begin
        matches_q <= matches_d;
      end
    end
  end

  assign done_o = (state_q == Done);

  // Instantiate an explicit prim_mubi4_sender for the good signal. The logic is that we don't want
  // to make the actual check multi-bit (doing so properly would mean replicating the 32-bit
  // comparator) but we *do* want to make sure a synthesis tool doesn't optimize away the 4-bit
  // signal. The barrier from the primitive ensures that won't happen.
  prim_mubi4_sender
  u_done_sender (
    .clk_i,
    .rst_ni,
    .mubi_i (mubi4_bool_to_mubi(matches_q)),
    .mubi_o (good_o)
  );

  assign alert_o = fsm_alert | start_alert | wait_addr_alert | done_addr_alert | addr_ctr_alert;

endmodule
