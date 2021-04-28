// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// The comparator inside the ROM checker
//
// This module is in charge of comparing the digest that was computed over the ROM data with the
// expected digest stored in the top few words.
//
//
// TODO: Think properly about hardening here. A glitch that messes up the comparison isn't a
//       show-stopper (because the attacker will still have the wrong CreatorRootKey in the key
//       manager), but glitching the FSM our counter could probably confuse some of the other blocks
//       that we communicate with.

`include "prim_assert.sv"

module rom_ctrl_compare #(
  parameter int NumWords = 2,
  parameter bit SkipCheck = 1'b1
) (
  input logic                        clk_i,
  input logic                        rst_ni,

  input logic                        start_i,
  output logic                       done_o,
  output logic                       good_o,

  // CSR inputs for DIGEST and EXP_DIGEST. Ordered with word 0 as LSB.
  input logic [NumWords*32-1:0]      digest_i,
  input logic [NumWords*32-1:0]      exp_digest_i,

  // To alert system
  output logic                       alert_o
);

  import prim_util_pkg::vbits;

  `ASSERT_INIT(NumWordsPositive_A, 0 < NumWords)

  localparam int AW = vbits(NumWords);

  localparam int unsigned EndAddrInt  = NumWords;
  localparam int unsigned LastAddrInt = NumWords - 1;

  // Note that if NumWords is a power of 2 then EndAddr will be zero. That's ok: we're just using a
  // comparison with EndAddr to check that the address counter hasn't started wandering around when
  // we're in the wrong state.
  localparam bit [AW-1:0] EndAddr     = EndAddrInt[AW-1:0];
  localparam bit [AW-1:0] LastAddr    = LastAddrInt[AW-1:0];

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
  typedef enum logic [4:0] {
    Waiting  = 5'b00100,
    Checking = 5'b10010,
    Done     = 5'b11001
  } state_e;

  logic [4:0]  state_q, state_d;
  logic        matches_q, matches_d;
  logic        fsm_alert;

  prim_flop #(.Width(5), .ResetValue({Waiting}))
  u_state_regs (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d_i    (state_d),
    .q_o    (state_q)
  );

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
  logic start_alert;
  assign start_alert = start_i && (state_q != Waiting);

  // addr_q should be zero when we're in the Waiting state
  logic wait_addr_alert;
  assign wait_addr_alert = (state_q == Waiting) && (addr_q != '0);

  // addr_q should be EndAddr when we're in the Done state
  logic done_addr_alert;
  assign done_addr_alert = (state_q == Done) && (addr_q != EndAddr);

  // Increment addr_q on each cycle when in Checking
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_q    <= '0;
      matches_q <= 1'b1;
    end else begin
      if (state_q == Checking) begin
        addr_q    <= addr_q + AW'(1);
        matches_q <= matches_d;
      end
    end
  end

  logic [AW+5-1:0] digest_idx;
  logic [31:0]     digest_word, exp_digest_word;
  assign digest_idx = {addr_q, 5'd31};
  assign digest_word = digest_i[digest_idx -: 32];
  assign exp_digest_word = exp_digest_i[digest_idx -: 32];
  assign matches_d = matches_q && (digest_word == exp_digest_word);

  assign done_o = (state_q == Done);
  assign good_o = matches_q | SkipCheck;

  assign alert_o = fsm_alert | start_alert | wait_addr_alert | done_addr_alert;

endmodule
