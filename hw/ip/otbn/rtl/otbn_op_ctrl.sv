// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Operation control for OTBN
 *
 * Tracks the operational state of OTBN, accepts commands from software and provides the value of
 * the STATUS register.
 */
module otbn_op_ctrl
  import otbn_pkg::*;
(
  input  logic       clk_i,
  input  logic       rst_ni,

  // CMD register write
  input  logic       cmd_valid_i,
  input  logic [7:0] cmd_i,

  // From the OTBN core
  input  logic       locking_i,
  input  logic       secure_wipe_running_i,
  input  logic       wfi_pending_i,
  input  logic       done_core_i,
  input  logic       mems_sec_wipe_i,

  // From the scramble controller
  input  logic       dmem_key_req_busy_i,
  input  logic       imem_key_req_busy_i,

  // To the OTBN core
  output logic       start_o,
  output logic       wfi_resume_o,

  // To the scramble controller
  output logic       dmem_sec_wipe_o,
  output logic       imem_sec_wipe_o,

  // Busy state and STATUS register value
  output logic       busy_execute_d_o,
  output logic       busy_execute_q_o,
  output status_e    status_d_o,
  output status_e    status_q_o,

  output logic       state_error_o
);

  op_ctrl_state_e state_d, state_q;

  logic cmd_execute, cmd_sec_wipe_dmem, cmd_sec_wipe_imem, cmd_resume;
  assign cmd_execute       = cmd_valid_i && (cmd_i == CmdExecute);
  assign cmd_sec_wipe_dmem = cmd_valid_i && (cmd_i == CmdSecWipeDmem);
  assign cmd_sec_wipe_imem = cmd_valid_i && (cmd_i == CmdSecWipeImem);
  assign cmd_resume        = cmd_valid_i && (cmd_i == CmdResume);

  // SEC_CM: OP_CTRL.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, op_ctrl_state_e, OpCtrlWipeInt)

  always_comb begin
    state_d         = state_q;
    start_o         = 1'b0;
    wfi_resume_o    = 1'b0;
    dmem_sec_wipe_o = 1'b0;
    imem_sec_wipe_o = 1'b0;
    state_error_o   = 1'b0;

    unique case (state_q)
      OpCtrlWipeInt: begin
        if (!secure_wipe_running_i) begin
          state_d = OpCtrlIdle;
        end
      end
      OpCtrlIdle: begin
        // A command in the cycle that OTBN starts locking is ignored.
        if (!locking_i) begin
          start_o         = cmd_execute;
          dmem_sec_wipe_o = cmd_sec_wipe_dmem;
          imem_sec_wipe_o = cmd_sec_wipe_imem;
        end

        if (cmd_execute && !locking_i) begin
          if (secure_wipe_running_i) begin
            state_d = OpCtrlExecWipeInt;
          end else begin
            state_d = OpCtrlExecute;
          end
        end else if (secure_wipe_running_i) begin
          state_d = OpCtrlWipeInt;
        end else if (cmd_sec_wipe_dmem && !locking_i) begin
          state_d = OpCtrlWipeDmem;
        end else if (cmd_sec_wipe_imem && !locking_i) begin
          state_d = OpCtrlWipeImem;
        end
      end
      OpCtrlExecute,
      OpCtrlExecWipeInt: begin
        dmem_sec_wipe_o = mems_sec_wipe_i;
        imem_sec_wipe_o = mems_sec_wipe_i;

        if (secure_wipe_running_i) begin
          if (done_core_i || wfi_pending_i) begin
            state_d = OpCtrlWipeInt;
          end else begin
            state_d = OpCtrlExecWipeInt;
          end
        end else if (wfi_pending_i) begin
          state_d = OpCtrlPaused;
        end else if (!done_core_i) begin
          state_d = OpCtrlExecute;
        end else begin
          state_d = OpCtrlIdle;
        end
      end
      OpCtrlPaused: begin
        dmem_sec_wipe_o = mems_sec_wipe_i;
        imem_sec_wipe_o = mems_sec_wipe_i;
        wfi_resume_o    = cmd_resume;

        if (cmd_resume) begin
          if (secure_wipe_running_i) begin
            state_d = OpCtrlExecWipeInt;
          end else if (wfi_pending_i) begin
            state_d = OpCtrlResume;
          end else begin
            state_d = OpCtrlExecute;
          end
        end else if (secure_wipe_running_i) begin
          state_d = OpCtrlWipeInt;
        end else if (!wfi_pending_i) begin
          state_d = OpCtrlIdle;
        end
      end
      OpCtrlResume: begin
        // The core still signals wfi_pending in this cycle, so it is ignored here.
        dmem_sec_wipe_o = mems_sec_wipe_i;
        imem_sec_wipe_o = mems_sec_wipe_i;

        if (secure_wipe_running_i) begin
          if (done_core_i) begin
            state_d = OpCtrlWipeInt;
          end else begin
            state_d = OpCtrlExecWipeInt;
          end
        end else if (done_core_i) begin
          state_d = OpCtrlIdle;
        end else begin
          state_d = OpCtrlExecute;
        end
      end
      OpCtrlWipeDmem: begin
        if (secure_wipe_running_i) begin
          state_d = OpCtrlWipeInt;
        end else if (!dmem_key_req_busy_i) begin
          state_d = OpCtrlIdle;
        end
      end
      OpCtrlWipeImem: begin
        if (secure_wipe_running_i) begin
          state_d = OpCtrlWipeInt;
        end else if (!imem_key_req_busy_i) begin
          state_d = OpCtrlIdle;
        end
      end
      OpCtrlLocked: begin
        // Terminal state
      end
      default: begin
        // SEC_CM: OP_CTRL.FSM.LOCAL_ESC
        // We should never get here. If we do (e.g. via a malicious glitch), error out immediately.
        state_error_o = 1'b1;
        state_d       = OpCtrlLocked;
      end
    endcase

    // SEC_CM: OP_CTRL.FSM.GLOBAL_ESC, OP_CTRL.FSM.LOCAL_ESC
    if (locking_i) begin
      state_d = OpCtrlLocked;
    end
  end

  assign busy_execute_d_o = state_d inside {OpCtrlExecute, OpCtrlExecWipeInt, OpCtrlResume};
  assign busy_execute_q_o = state_q inside {OpCtrlExecute, OpCtrlExecWipeInt, OpCtrlResume};

  assign status_d_o = op_ctrl_state_to_status(state_d);
  assign status_q_o = op_ctrl_state_to_status(state_q);

  `ASSERT(OtbnOpCtrlLocalEscCntrMeasure_A, state_error_o |=> state_q == OpCtrlLocked)
  `ASSERT(OtbnOpCtrlLockedTerminal_A, state_q == OpCtrlLocked |=> state_q == OpCtrlLocked)
  `ASSERT(OtbnOpCtrlNoStartWhenLocking_A, locking_i |-> !start_o)

endmodule
