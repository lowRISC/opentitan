// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: interface between a req/ack interface and a fifo
//

module entropy_src_ack_sm (
  input logic                clk_i,
  input logic                rst_ni,

  input logic                req_i,
  output logic               ack_o,
  input logic                fifo_not_empty_i,
  output logic               fifo_pop_o
);

  // Encoding generated with ./sparse-fsm-encode.py -d 3 -m 3 -n 6 -s 3584999330
  // Hamming distance histogram:
  //
  // 0: --
  // 1: --
  // 2: --
  // 3: |||||||||||||||||||| (66.67%)
  // 4: |||||||||| (33.33%)
  // 5: --
  // 6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  //

  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    Idle      = 6'b010110, // idle
    AckImmed  = 6'b111111, // ack the request immediately
    AckWait   = 6'b111000  // wait until the fifo has an entry
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
    unique case (state_q)
      Idle: begin
        if (req_i) begin
          if (fifo_not_empty_i) begin
            state_d = AckImmed;
          end else begin
            state_d = AckWait;
          end
        end
      end
      AckImmed: begin
        ack_o = 1'b1;
        fifo_pop_o = 1'b1;
        state_d = Idle;
      end
      AckWait: begin
        if (fifo_not_empty_i) begin
          ack_o = 1'b1;
          fifo_pop_o = 1'b1;
          state_d = Idle;
        end
      end
      default: state_d = Idle;
    endcase
  end

endmodule
