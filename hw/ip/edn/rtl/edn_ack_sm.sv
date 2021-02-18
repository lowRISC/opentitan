// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: interface between a req/ack interface and a fifo
//

module edn_ack_sm (
  input logic                clk_i,
  input logic                rst_ni,

  input logic                req_i,
  output logic               ack_o,
  input logic                fifo_not_empty_i,
  output logic               fifo_pop_o,
  output logic               ack_sm_err_o
);

// Encoding generated with:
// $ ./util/design/sparse-fsm-encode.py -d 3 -m 4 -n 6 \
//      -s 2299232677 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||||||||||| (50.00%)
//  4: ||||||||||||| (33.33%)
//  5: |||||| (16.67%)
//  6: --
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 5
// Minimum Hamming weight: 1
// Maximum Hamming weight: 4
//

  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    Idle      = 6'b101101, // idle (hamming distance = 3)
    DataWait  = 6'b111010, // wait for data to return
    AckPls    = 6'b010110, // signal ack to endpoint TODO: regen states
    Error     = 6'b001000  // illegal state reached and hang
  } state_e;

  state_e state_d, state_q;

  logic [StateWidth-1:0] state_raw_q;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(Idle))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d ),
    .q_o ( state_raw_q )
  );

  assign state_q = state_e'(state_raw_q);

  always_comb begin
    state_d = state_q;
    ack_o = 1'b0;
    fifo_pop_o = 1'b0;
    ack_sm_err_o = 1'b0;
    unique case (state_q)
      Idle: begin
        if (req_i) begin
          if (fifo_not_empty_i) begin
            fifo_pop_o = 1'b1;
          end
          state_d = DataWait;
        end
      end
      DataWait: begin
        if (fifo_not_empty_i) begin
          state_d = AckPls;
        end
      end
      AckPls: begin
        ack_o = 1'b1;
        state_d = Idle;
      end
      Error: begin
        ack_sm_err_o = 1'b1;
      end
      default: state_d = Error;
    endcase
  end

endmodule
