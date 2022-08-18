// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src main state machine module
//
//   determines when new entropy is ready to be forwarded

module entropy_src_main_sm #(
  localparam int StateWidth = 9
) (
  input logic                   clk_i,
  input logic                   rst_ni,

  input logic                   enable_i,
  input logic                   fw_ov_ent_insert_i,
  input logic                   fw_ov_sha3_start_i,
  input logic                   ht_done_pulse_i,
  input logic                   ht_fail_pulse_i,
  input logic                   alert_thresh_fail_i,
  output logic                  rst_alert_cntr_o,
  input logic                   bypass_mode_i,
  input logic                   main_stage_rdy_i,
  input logic                   bypass_stage_rdy_i,
  input logic                   sha3_state_vld_i,
  output logic                  main_stage_push_o,
  output logic                  bypass_stage_pop_o,
  output logic                  boot_phase_done_o,
  output logic                  sha3_start_o,
  output logic                  sha3_process_o,
  output prim_mubi_pkg::mubi4_t sha3_done_o,
  output logic                  cs_aes_halt_req_o,
  input logic                   cs_aes_halt_ack_i,
  input logic                   local_escalate_i,
  output logic                  main_sm_alert_o,
  output logic                  main_sm_idle_o,
  output logic [StateWidth-1:0] main_sm_state_o,
  output logic                  main_sm_err_o
);

// Encoding generated with:
// $ ./util/design/sparse-fsm-encode.py -d 3 -m 21 -n 9 \
//      -s 2359261201 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||| (19.05%)
//  4: |||||||||||||||||||| (30.48%)
//  5: ||||||||||||||||| (26.19%)
//  6: |||||||||| (15.71%)
//  7: ||| (5.71%)
//  8: | (2.38%)
//  9:  (0.48%)
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 9
// Minimum Hamming weight: 1
// Maximum Hamming weight: 8
//

  typedef enum logic [StateWidth-1:0] {
    Idle              = 9'b011110101, // idle
    BootHTRunning     = 9'b111010010, // boot mode, wait for health test done pulse
    BootPostHTChk     = 9'b101101110, // boot mode, wait for post health test packer not empty state
    BootPhaseDone     = 9'b010001110, // boot mode, stay here until master enable is off
    StartupHTStart    = 9'b000101100, // startup mode, pulse the sha3 start input
    StartupPhase1     = 9'b100000001, // startup mode, look for first test pass/fail
    StartupPass1      = 9'b110100101, // startup mode, look for first test pass/fail, done if pass
    StartupFail1      = 9'b000010111, // startup mode, look for second fail, alert if fail
    ContHTStart       = 9'b001000000, // continuous test mode, pulse the sha3 start input
    ContHTRunning     = 9'b110100010, // continuous test mode, wait for health test done pulse
    FWInsertStart     = 9'b011000011, // fw ov mode, start the sha3 block
    FWInsertMsg       = 9'b001011001, // fw ov mode, insert fw message into sha3 block
    Sha3MsgDone       = 9'b100001111, // sha3 mode, all input messages added, ready to process
    Sha3Prep          = 9'b011111000, // sha3 mode, request csrng arb to reduce power
    Sha3Process       = 9'b010111111, // sha3 mode, pulse the sha3 process input
    Sha3Valid         = 9'b101110001, // sha3 mode, wait for sha3 valid indication
    Sha3Done          = 9'b110011000, // sha3 mode, capture sha3 result, pulse done input
    Sha3Quiesce       = 9'b111001101, // sha3 mode, goto alert state or continuous check mode
    AlertState        = 9'b111111011, // if some alert condition occurs, pulse an alert indication
    AlertHang         = 9'b101011100, // after pulsing alert signal, hang here until sw handles
    Error             = 9'b100111101  // illegal state reached and hang
  } state_e;

  state_e state_d, state_q;

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, Idle)

  assign main_sm_state_o = state_q;

  always_comb begin
    state_d = state_q;
    rst_alert_cntr_o = 1'b0;
    main_stage_push_o = 1'b0;
    bypass_stage_pop_o = 1'b0;
    boot_phase_done_o = 1'b0;
    sha3_start_o = 1'b0;
    sha3_process_o = 1'b0;
    sha3_done_o = prim_mubi_pkg::MuBi4False;
    cs_aes_halt_req_o = 1'b0;
    main_sm_alert_o = 1'b0;
    main_sm_idle_o = 1'b0;
    main_sm_err_o = 1'b0;
    unique case (state_q)
      Idle: begin
        main_sm_idle_o = 1'b1;
        if (enable_i) begin
          // running fw override mode and in sha3 mode
          if (fw_ov_ent_insert_i && !bypass_mode_i) begin
            state_d = FWInsertStart;
          // running in bypass_mode and not fw override mode
          end else if (bypass_mode_i && !fw_ov_ent_insert_i) begin
            state_d = BootHTRunning;
          // running in bypass_mode and fw override mode
          end else if (bypass_mode_i && fw_ov_ent_insert_i) begin
            state_d = Idle;
          end else begin
            state_d = StartupHTStart;
          end
        end
      end
      BootHTRunning: begin
        if (!enable_i) begin
          state_d = Idle;
        end else if (bypass_stage_rdy_i) begin
          // pop if prior ht phase failed
          bypass_stage_pop_o = 1'b1;
        end else begin
          if (ht_done_pulse_i) begin
            if (ht_fail_pulse_i) begin
              if (alert_thresh_fail_i) begin
                state_d = AlertState;
              end else begin
                state_d = Idle;
              end
            end else begin
              state_d = BootPostHTChk;
            end
          end
        end
      end
      BootPostHTChk: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (!bypass_stage_rdy_i) begin
          end else begin
            rst_alert_cntr_o = 1'b1;
            bypass_stage_pop_o = 1'b1;
            main_stage_push_o = 1'b1;
            state_d = BootPhaseDone;
          end
        end
      end
      BootPhaseDone: begin
        boot_phase_done_o = 1'b1;
        if (!enable_i) begin
          state_d = Idle;
        end
        // Even when stalled we keep monitoring for alerts and maintaining  alert statistics.
        // However, we don't signal alerts or clear HT stats in FW_OV mode.
        if(!fw_ov_ent_insert_i && ht_done_pulse_i) begin
          if (alert_thresh_fail_i) begin
            state_d = AlertState;
          end else if (!ht_fail_pulse_i) begin
            rst_alert_cntr_o = 1'b1;
          end
        end
      end
      StartupHTStart: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          sha3_start_o = 1'b1;
          state_d = StartupPhase1;
        end
      end
      StartupPhase1: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (ht_done_pulse_i) begin
            if (ht_fail_pulse_i) begin
              state_d = StartupFail1;
            end else begin
              state_d = StartupPass1;
            end
          end
        end
      end
      StartupPass1: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (ht_done_pulse_i) begin
            if (ht_fail_pulse_i) begin
              state_d = StartupFail1;
            end else begin
              // Passed two consecutive tests
              state_d = Sha3MsgDone;
            end
          end
        end
      end
      StartupFail1: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (ht_done_pulse_i) begin
            if (ht_fail_pulse_i) begin
              // Failed two consecutive tests
              state_d = AlertState;
            end else begin
              state_d = StartupPass1;
            end
          end
        end
      end
      ContHTStart: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          sha3_start_o = 1'b1;
          state_d = ContHTRunning;
        end
      end
      ContHTRunning: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (ht_done_pulse_i) begin
            if (alert_thresh_fail_i) begin
              state_d = AlertState;
            end else if (!ht_fail_pulse_i) begin
              state_d = Sha3MsgDone;
            end
          end
        end
      end
      FWInsertStart: begin
        if (fw_ov_sha3_start_i || !enable_i) begin
          sha3_start_o = 1'b1;
          state_d = FWInsertMsg;
        end
      end
      FWInsertMsg: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (!fw_ov_sha3_start_i) begin
            state_d = Sha3MsgDone;
          end
        end
      end
      Sha3MsgDone: begin
        state_d = Sha3Prep;
      end
      Sha3Prep: begin
        // for normal or halt cases, always prevent a power spike
        cs_aes_halt_req_o = 1'b1;
        if (cs_aes_halt_ack_i) begin
          state_d = Sha3Process;
        end
      end
      Sha3Process: begin
        cs_aes_halt_req_o = 1'b1;
        // The SHA control is asynchronous from the HT's in FW_OV mode
        // breaking some of the timing assumptions associated with this
        // alert clear pulse.  This makes predicting the alert count registers
        // harder, and even though the alerts are surpressed in this mode
        // the counters are still scoreboarded, so we supress this clear
        // pulse in FW_OV insert mode.
        rst_alert_cntr_o = ~fw_ov_ent_insert_i;
        sha3_process_o = 1'b1;
        state_d = Sha3Valid;
      end
      Sha3Valid: begin
        cs_aes_halt_req_o = 1'b1;
        if (sha3_state_vld_i) begin
          state_d = Sha3Done;
        end
      end
      Sha3Done: begin
        if (!enable_i) begin
          sha3_done_o = prim_mubi_pkg::MuBi4True;
          state_d = Idle;
        end else begin
          if (main_stage_rdy_i) begin
            sha3_done_o = prim_mubi_pkg::MuBi4True;
            main_stage_push_o = 1'b1;
            if (fw_ov_ent_insert_i) begin
              state_d = Idle;
            end else begin
              state_d = Sha3Quiesce;
            end
          end
        end
      end
      Sha3Quiesce: begin
        if (!enable_i) begin
          state_d = Idle;
        end else if (alert_thresh_fail_i) begin
          state_d = AlertState;
        end else begin
          state_d = ContHTStart;
        end
      end
      AlertState: begin
        main_sm_alert_o = 1'b1;
        state_d = AlertHang;
      end
      AlertHang: begin
        if (!enable_i) begin
          state_d = Idle;
        end
      end
      Error: begin
        main_sm_err_o = 1'b1;
      end
      default: state_d = Error;
    endcase
    if (local_escalate_i) begin
      state_d = Error;
    end
  end

endmodule
