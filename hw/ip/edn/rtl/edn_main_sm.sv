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
  input logic                cmd_sent_i
);

  // Encoding generated with ./sparse-fsm-encode.py -d 3 -m 7 -n 6 -s 4153446945
  // Hamming distance histogram:
  //
  // 0: --
  // 1: --
  // 2: --
  // 3: |||||||||||||||||||| (57.14%)
  // 4: ||||||||||||||| (42.86%)
  // 5: --
  // 6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  //

  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    Idle          = 6'b011000, // idle (hamming distance = 3)
    AckWait       = 6'b110001, // wait for csrng req ack
    Dispatch      = 6'b000100, // dispatch the next cmd after ack
    CaptGenCnt    = 6'b101101, // capture the generate fifo count
    SendGenCmd    = 6'b000011, // send the generate cmd req
    CaptReseedCnt = 6'b101010, // capture the reseed fifo count
    SendReseedCmd = 6'b011111  // send the reseed cmd req
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
      default: state_d = Idle;
    endcase
  end

endmodule
