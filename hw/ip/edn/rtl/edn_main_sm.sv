// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: edn csrng application request state machine module
//
//   does hardware-based csrng app interface command requests

module edn_main_sm (
  input logic                clk_i,
  input logic                rst_ni,

  input logic                auto_req_mode_i,
  output logic               seq_auto_req_mode_o,
  output logic               auto_req_mode_end_o,
  input logic                csrng_cmd_ack_i,
  output logic               capt_gencmd_fifo_cnt_o,
  output logic               send_gencmd_o,
  input logic                max_reqs_cnt_zero_i,
  output logic               capt_rescmd_fifo_cnt_o,
  output logic               send_rescmd_o,
  input logic                cmd_sent_i,
  output logic               main_sm_err_o
);

// Encoding generated with:
// $ ./util/design/sparse-fsm-encode.py -d 3 -m 8 -n 6 \
//      -s 3370065314 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||||||||||| (57.14%)
//  4: ||||||||||||||| (42.86%)
//  5: --
//  6: --
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 4
// Minimum Hamming weight: 1
// Maximum Hamming weight: 5
//

  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    Idle          = 6'b111011, // idle (hamming distance = 3)
    AckWait       = 6'b010111, // wait for csrng req ack
    Dispatch      = 6'b011100, // dispatch the next cmd after ack
    CaptGenCnt    = 6'b110000, // capture the generate fifo count
    SendGenCmd    = 6'b001001, // send the generate cmd req
    CaptReseedCnt = 6'b101110, // capture the reseed fifo count
    SendReseedCmd = 6'b000010, // send the reseed cmd req
    Error         = 6'b100101  // illegal state reached and hang
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
    capt_gencmd_fifo_cnt_o = 1'b0;
    send_gencmd_o = 1'b0;
    capt_rescmd_fifo_cnt_o = 1'b0;
    send_rescmd_o = 1'b0;
    seq_auto_req_mode_o = 1'b1;
    auto_req_mode_end_o = 1'b0;
    main_sm_err_o = 1'b0;
    unique case (state_q)
      Idle: begin
        seq_auto_req_mode_o = 1'b0;
        if (auto_req_mode_i) begin
          state_d = AckWait;
        end
      end
      AckWait: begin
        if (csrng_cmd_ack_i) begin
          state_d = Dispatch;
        end
      end
      Dispatch: begin
        if (!auto_req_mode_i) begin
          auto_req_mode_end_o = 1'b1;
          state_d = Idle;
        end else begin
          if (max_reqs_cnt_zero_i) begin
            state_d = CaptReseedCnt;
          end else begin
            state_d = CaptGenCnt;
          end
        end
      end
      CaptGenCnt: begin
        capt_gencmd_fifo_cnt_o = 1'b1;
        state_d = SendGenCmd;
      end
      SendGenCmd: begin
        send_gencmd_o = 1'b1;
        if (cmd_sent_i) begin
          state_d = AckWait;
        end
      end
      CaptReseedCnt: begin
        capt_rescmd_fifo_cnt_o = 1'b1;
        state_d = SendReseedCmd;
      end
      SendReseedCmd: begin
        send_rescmd_o = 1'b1;
        if (cmd_sent_i) begin
          state_d = AckWait;
        end
      end
      Error: begin
        main_sm_err_o = 1'b1;
      end
      default: state_d = Error;
    endcase
  end

endmodule
