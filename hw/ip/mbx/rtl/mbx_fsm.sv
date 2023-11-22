// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module mbx_fsm #(
  parameter bit CfgOmbx = 1'b1   // 1'b1: Obmbx, 1'b0: Ibmbx
) (
  input  logic clk_i,
  input  logic rst_ni,
  // Control input signals
  input  logic mbx_range_valid_i,
  input  logic hostif_abort_ack_i,
  input  logic mbx_error_set_i,
  input  logic sysif_control_abort_set_i,
  input  logic sys_read_all_i,
  input  logic writer_close_mbx_i,
  input  logic writer_last_word_written_i,
  input  logic writer_write_valid_i,
  // Status signals
  output logic mbx_empty_o,
  output logic mbx_write_o,
  output logic mbx_read_o,
  output logic mbx_sys_abort_o,
  output logic mbx_ready_update_o,
  output logic mbx_ready_o,
  output logic mbx_irq_ready_o,
  output logic mbx_irq_abort_o,
  output logic mbx_state_error_o
);
  typedef enum logic [2:0] {
    MbxIdle          = 3'b000,
    MbxWrite         = 3'b001,
    MbxWaitFinalWord = 3'b010,
    MbxRead          = 3'b011,
    MbxError         = 3'b100,
    MbxSysAbortHost  = 3'b101
  } mbx_ctrl_state_e;

  mbx_ctrl_state_e ctrl_state_q, ctrl_state_d;

  // Following cast is needed to avoid conversion errors between mbx_ctrl_state_e <-> logic
  logic [$bits(mbx_ctrl_state_e)-1:0] ctrl_state_logic;
  assign ctrl_state_q = mbx_ctrl_state_e'(ctrl_state_logic);

  prim_flop #(
    .Width($bits(mbx_ctrl_state_e)),
    .ResetValue({MbxIdle})
  ) aff_ctrl_state_q (
    .clk_i ( clk_i            ),
    .rst_ni( rst_ni           ),
    .d_i   ( ctrl_state_d     ),
    .q_o   ( ctrl_state_logic )
  );

  // Control signals for external usage
  logic mbx_idle;
  assign mbx_idle        = (ctrl_state_q == MbxIdle);
  assign mbx_empty_o     = mbx_idle & mbx_range_valid_i;
  assign mbx_write_o     = (ctrl_state_q == MbxWrite);
  assign mbx_read_o      = (ctrl_state_q == MbxRead);
  assign mbx_sys_abort_o = (ctrl_state_q == MbxSysAbortHost);
  // The transition to the abort state marks the abort interrupt generation
  assign mbx_irq_abort_o = (ctrl_state_d == MbxSysAbortHost);
  // The transition to the read state marks the ready interrupt generation
  assign mbx_irq_ready_o  = (ctrl_state_d == MbxRead);

  logic ombx_set_ready, ombx_clear_ready;
  // Outbound mailbox is Ready, but only if not simultaneous with the exceptional conditions that
  // demand clearing of the Ready status bit.
  assign ombx_set_ready = CfgOmbx
                            & mbx_idle
                            & mbx_range_valid_i
                            & writer_close_mbx_i;

  // MbxRead is a common state for imbx and ombx
  // Exit of MbxRead is used to clear imbx.Busy and ombx.Ready.
  // This must also happen when an Error, Abort or FW-initiated reset occurs.
  assign ombx_clear_ready = CfgOmbx & (mbx_error_set_i |
                                       sysif_control_abort_set_i |
                                       hostif_abort_ack_i |
                                       mbx_read_o & sys_read_all_i);

  assign mbx_ready_update_o = CfgOmbx & (ombx_set_ready | ombx_clear_ready);  // MUTEX(set,clr)
  assign mbx_ready_o        = !ombx_clear_ready;  // Clearing overrules setting.

  always_comb begin
    ctrl_state_d      = ctrl_state_q;
    mbx_state_error_o = 1'b0;

    // Acknowledgement of an Abort request may occur at any time, with the FSM in any state.
    if (hostif_abort_ack_i) begin
      ctrl_state_d = MbxIdle;
    end else begin
      unique case (ctrl_state_q)
        MbxIdle: begin
          if (CfgOmbx) begin
            if (mbx_range_valid_i & writer_close_mbx_i) begin
              ctrl_state_d = MbxRead;
            end
          end else begin
            if (mbx_range_valid_i & writer_write_valid_i) begin
              ctrl_state_d = MbxWrite;
            end
          end

          // If system wants to error or abort, it has the highest priority
          if (mbx_error_set_i) begin
            ctrl_state_d = MbxError;
          end else if (sysif_control_abort_set_i) begin
            ctrl_state_d = MbxSysAbortHost;
          end
        end

        // Inbound mailbox being written by the system = writer
        // Outbound mailbox: not applicable
        MbxWrite: begin
          if (mbx_error_set_i) begin                     // Host asserts an error
            ctrl_state_d = MbxError;
          end else if (sysif_control_abort_set_i) begin  // System wants to abort
            ctrl_state_d = MbxSysAbortHost;
          end else if (writer_close_mbx_i) begin  // Writer decided to close the mailbox
            if (writer_last_word_written_i) begin
              ctrl_state_d = MbxRead;
            end else begin
              ctrl_state_d = MbxWaitFinalWord;
            end
          end
        end

        // Inbound mailbox being written by the system = writer
        // Outbound mailbox: not applicable
        MbxWaitFinalWord: begin
          if (mbx_error_set_i) begin                      // Host asserts an error
            ctrl_state_d = MbxError;
          end else if (sysif_control_abort_set_i) begin   // System wants to abort
            ctrl_state_d = MbxSysAbortHost;
          end else if (writer_last_word_written_i) begin
           ctrl_state_d = MbxRead;
          end
        end

        // Inbound mailbox being read by the reader = host
        // Outbound mailbox being read by the reader = system
        MbxRead: begin
          if (mbx_error_set_i) begin                      // Host asserts an error
            ctrl_state_d = MbxError;
          end else if (sysif_control_abort_set_i) begin   // System wants to abort
            ctrl_state_d = MbxSysAbortHost;
          end else if (sys_read_all_i) begin
            // Inbound and outbound mailbox go back to idle after all data has
            // been read by the sys requester
            ctrl_state_d = MbxIdle;
          end
        end

        // Wait for the abort request to occur
        MbxError: begin
          if (sysif_control_abort_set_i) begin
            ctrl_state_d = MbxSysAbortHost;
          end
        end

        MbxSysAbortHost: begin
          // Wait for the host to acknowledge the abort; handled above.
        end

        default: begin
          // Should not reach this
          ctrl_state_d      = MbxIdle;
          mbx_state_error_o = 1'b1;
        end
      endcase
    end
  end
endmodule
