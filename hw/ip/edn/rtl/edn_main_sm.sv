// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: edn csrng application request state machine module
//
//   does hardware-based csrng app interface command requests

module edn_main_sm import edn_pkg::*;
(
  input logic                   clk_i,
  input logic                   rst_ni,

  input logic                   edn_enable_i,
  input logic                   boot_req_mode_i,
  input logic                   auto_req_mode_i,
  input logic                   sw_cmd_req_load_i,
  output logic                  sw_cmd_mode_o,
  output logic                  boot_wr_ins_cmd_o,
  output logic                  boot_send_ins_cmd_o,
  output logic                  boot_wr_gen_cmd_o,
  output logic                  boot_wr_uni_cmd_o,
  output logic                  accept_sw_cmds_pulse_o,
  output logic                  main_sm_done_pulse_o,
  input logic                   csrng_cmd_ack_i,
  output logic                  capt_gencmd_fifo_cnt_o,
  output logic                  send_gencmd_o,
  input logic                   max_reqs_cnt_zero_i,
  output logic                  capt_rescmd_fifo_cnt_o,
  output logic                  send_rescmd_o,
  input logic                   cmd_sent_i,
  output logic                  auto_req_mode_busy_o,
  output logic [StateWidth-1:0] main_sm_state_o,
  input logic                   csrng_ack_err_i,
  output logic                  reject_csrng_entropy_o,
  input logic                   local_escalate_i,
  output logic                  main_sm_err_o
);

  state_e state_d, state_q;

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, Idle)

  assign main_sm_state_o = state_q;

  always_comb begin
    state_d                = state_q;
    boot_wr_ins_cmd_o      = 1'b0;
    boot_send_ins_cmd_o    = 1'b0;
    boot_wr_gen_cmd_o      = 1'b0;
    boot_wr_uni_cmd_o      = 1'b0;
    accept_sw_cmds_pulse_o = 1'b0;
    auto_req_mode_busy_o   = 1'b0;
    capt_gencmd_fifo_cnt_o = 1'b0;
    send_gencmd_o          = 1'b0;
    capt_rescmd_fifo_cnt_o = 1'b0;
    send_rescmd_o          = 1'b0;
    main_sm_done_pulse_o   = 1'b0;
    main_sm_err_o          = 1'b0;
    reject_csrng_entropy_o = 1'b0;
    sw_cmd_mode_o         = 1'b0;
    unique case (state_q)
      Idle: begin
        if (boot_req_mode_i && edn_enable_i) begin
          state_d = BootLoadIns;
        end else if (auto_req_mode_i && edn_enable_i) begin
          accept_sw_cmds_pulse_o = 1'b1;
          sw_cmd_mode_o = 1'b1;
          state_d = AutoLoadIns;
        end else if (edn_enable_i) begin
          main_sm_done_pulse_o = 1'b1;
          accept_sw_cmds_pulse_o = 1'b1;
          sw_cmd_mode_o = 1'b1;
          state_d = SWPortMode;
        end
      end
      BootLoadIns: begin
        boot_wr_ins_cmd_o = 1'b1;
        boot_send_ins_cmd_o = 1'b1;
        state_d = BootInsAckWait;
      end
      BootInsAckWait: begin
        boot_send_ins_cmd_o = 1'b1;
        if (csrng_cmd_ack_i) begin
          state_d = BootLoadGen;
        end
      end
      BootLoadGen: begin
        boot_wr_gen_cmd_o = 1'b1;
        state_d = BootGenAckWait;
      end
      BootGenAckWait: begin
        if (csrng_cmd_ack_i) begin
          state_d = BootPulse;
        end
      end
      BootPulse: begin
        state_d = BootDone;
      end
      BootDone: begin
        if (!boot_req_mode_i) begin
          state_d = BootLoadUni;
        end
      end
      BootLoadUni: begin
        boot_wr_uni_cmd_o = 1'b1;
        state_d = BootUniAckWait;
      end
      BootUniAckWait: begin
        if (csrng_cmd_ack_i) begin
          main_sm_done_pulse_o = 1'b1;
          state_d = Idle;
        end
      end
      //-----------------------------------
      AutoLoadIns: begin
        sw_cmd_mode_o = 1'b1;
        if (sw_cmd_req_load_i) begin
          state_d = AutoFirstAckWait;
        end
      end
      AutoFirstAckWait: begin
        sw_cmd_mode_o = 1'b1;
        if (csrng_cmd_ack_i) begin
          state_d = AutoDispatch;
        end
      end
      AutoAckWait: begin
        auto_req_mode_busy_o = 1'b1;
        if (csrng_cmd_ack_i) begin
          state_d = AutoDispatch;
        end
      end
      AutoDispatch: begin
        auto_req_mode_busy_o = 1'b1;
        if (!auto_req_mode_i) begin
          main_sm_done_pulse_o = 1'b1;
          state_d = Idle;
        end else begin
          if (max_reqs_cnt_zero_i) begin
            state_d = AutoCaptReseedCnt;
          end else begin
            state_d = AutoCaptGenCnt;
          end
        end
      end
      AutoCaptGenCnt: begin
        auto_req_mode_busy_o = 1'b1;
        capt_gencmd_fifo_cnt_o = 1'b1;
        state_d = AutoSendGenCmd;
      end
      AutoSendGenCmd: begin
        auto_req_mode_busy_o = 1'b1;
        send_gencmd_o = 1'b1;
        if (cmd_sent_i) begin
          state_d = AutoAckWait;
        end
      end
      AutoCaptReseedCnt: begin
        auto_req_mode_busy_o = 1'b1;
        capt_rescmd_fifo_cnt_o = 1'b1;
        state_d = AutoSendReseedCmd;
      end
      AutoSendReseedCmd: begin
        auto_req_mode_busy_o = 1'b1;
        send_rescmd_o = 1'b1;
        if (cmd_sent_i) begin
          state_d = AutoAckWait;
        end
      end
      SWPortMode: begin
        sw_cmd_mode_o = 1'b1;
      end
      RejectCsrngEntropy: begin
        reject_csrng_entropy_o = 1'b1;
      end
      Error: begin
        main_sm_err_o = 1'b1;
      end
      default: begin
        state_d = Error;
        main_sm_err_o = 1'b1;
      end
    endcase

    if (local_escalate_i || csrng_ack_err_i) begin
      // Either move into RejectCsrngEntropy or Error but don't move out of Error as it's terminal.
      state_d = local_escalate_i ? Error :
                state_q == Error ? Error : RejectCsrngEntropy;
      // Tie off outputs, except for main_sm_err_o, auto_req_mode_busy_o, boot_send_ins_cmd_o,
      // sw_cmd_mode_o and reject_csrng_entropy_o.
      boot_wr_ins_cmd_o      = 1'b0;
      boot_wr_gen_cmd_o      = 1'b0;
      boot_wr_uni_cmd_o      = 1'b0;
      accept_sw_cmds_pulse_o = 1'b0;
      capt_gencmd_fifo_cnt_o = 1'b0;
      send_gencmd_o          = 1'b0;
      capt_rescmd_fifo_cnt_o = 1'b0;
      send_rescmd_o          = 1'b0;
      main_sm_done_pulse_o   = 1'b0;
    end else if (!edn_enable_i && state_q inside {BootLoadIns, BootInsAckWait, BootLoadGen,
                                                  BootGenAckWait, BootLoadUni, BootUniAckWait,
                                                  BootPulse, BootDone,
                                                  AutoLoadIns, AutoFirstAckWait, AutoAckWait,
                                                  AutoDispatch, AutoCaptGenCnt, AutoSendGenCmd,
                                                  AutoCaptReseedCnt, AutoSendReseedCmd,
                                                  SWPortMode, RejectCsrngEntropy
                                                 }) begin
      // Only go to idle if the state is legal and not Idle or Error.
      // Even when disabled, illegal states must result in a transition to Error.
      state_d = Idle;
      // Tie off outputs, except for main_sm_err_o.
      boot_wr_ins_cmd_o      = 1'b0;
      boot_send_ins_cmd_o    = 1'b0;
      boot_wr_gen_cmd_o      = 1'b0;
      boot_wr_uni_cmd_o      = 1'b0;
      accept_sw_cmds_pulse_o = 1'b0;
      auto_req_mode_busy_o   = 1'b0;
      capt_gencmd_fifo_cnt_o = 1'b0;
      send_gencmd_o          = 1'b0;
      capt_rescmd_fifo_cnt_o = 1'b0;
      send_rescmd_o          = 1'b0;
      sw_cmd_mode_o          = 1'b0;
      reject_csrng_entropy_o = 1'b0;
      main_sm_done_pulse_o   = 1'b1;
    end
  end

  // The `local_escalate_i` includes `main_sm_err_o`.
  // The following assertion ensures the Error state is stable until reset.
  // With `FpvSecCm` prefix, this assertion will added to weekly FPV sec_cm regression.
  `ASSERT(FpvSecCmErrorStEscalate_A, state_q == Error |-> local_escalate_i)

  // This assertion does not have `FpvSecCm` prefix because the sec_cm FPV environment will
  // blackbox the `prim_sparse_fsm` `state_q` output.
  `ASSERT(ErrorStStable_A, state_q == Error |=> $stable(state_q))
endmodule
