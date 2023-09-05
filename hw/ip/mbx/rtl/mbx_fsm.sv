// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module mbx_fsm #(
  parameter bit CfgObMbx = 1'b1   // 1'b1: Obmbx, 1'b0: Ibmbx
) (
  input  logic clk_i,
  input  logic rst_ni,
  // Control input signals
  input  logic mbx_range_valid_i,
  input  logic hostif_abort_ack_i,
  input  logic hostif_status_error_set_i,
  input  logic hostif_status_busy_clear_i,
  input  logic sysif_control_abort_set_i,
  input  logic sys_read_all_i,
  input  logic writer_write_valid_i,
  input  logic writer_close_mbx_i,
  // Status signals
  output logic mbx_empty_o,
  output logic mbx_write_o,
  output logic mbx_read_o,
  output logic mbx_sys_abort_o,
  output logic mbx_ob_ready_update_o,
  output logic mbx_ob_ready_o,
  output logic mbx_state_error_o
);
  typedef enum logic [1:0] {
    MbxIdle         = 2'b00,
    MbxWrite        = 2'b01,
    MbxRead         = 2'b10,
    MbxSysAbortHost = 2'b11
  } mbx_ctrl_state_e;

  mbx_ctrl_state_e ctrl_state_q, ctrl_state_d;

  // Following cast is needed to avoid conversion errors between mbx_ctrl_state_e <-> logic
  logic [$bits(mbx_ctrl_state_e)-1:0] ctrl_state_logic;
  assign ctrl_state_q = mbx_ctrl_state_e'(ctrl_state_logic);

  prim_flop #(
    .Width($bits(mbx_ctrl_state_e)),
    .ResetValue(MbxIdle)
  ) aff_ctrl_state_q (
    .clk_i ( clk_i            ),
    .rst_ni( rst_ni           ),
    .d_i   ( ctrl_state_d     ),
    .q_o   ( ctrl_state_logic )
  );

  // Control signals for external usage
  logic mbx_idle;
  assign  mbx_idle        = (ctrl_state_q == MbxIdle);
  assign  mbx_empty_o     = mbx_idle & mbx_range_valid_i;
  assign  mbx_write_o     = (ctrl_state_q == MbxWrite);
  assign  mbx_read_o      = (ctrl_state_q == MbxRead);
  assign  mbx_sys_abort_o = (ctrl_state_q == MbxSysAbortHost);

  logic ob_set_ready, ob_clear_ready;
  // Outbound mailbox is ready
  assign ob_set_ready = CfgObMbx
                            & mbx_idle
                            & mbx_range_valid_i & writer_close_mbx_i
                            & ~sysif_control_abort_set_i;

  // MbxRead is a common state for imbx and ombx
  // Exit of MbxRead is used to clear imbx.Busy and ombx.Ready
  assign ob_clear_ready = CfgObMbx & (hostif_status_error_set_i |
                                      sysif_control_abort_set_i |
                                      mbx_read_o & sys_read_all_i);

  assign mbx_ob_ready_update_o = CfgObMbx & (ob_set_ready | ob_clear_ready);  // MUTEX(set,clr)
  assign mbx_ob_ready_o        = ob_set_ready;

  always_comb begin
    ctrl_state_d      = ctrl_state_q;
    mbx_state_error_o = 1'b0;

    unique case (ctrl_state_q)
      MbxIdle: begin
        if (CfgObMbx) begin
          if (mbx_range_valid_i & writer_close_mbx_i) begin
            ctrl_state_d = MbxRead;
          end
        end else begin
          if (mbx_range_valid_i & writer_write_valid_i) begin
            ctrl_state_d = MbxWrite;
          end
        end

        // If system wants to abort, it has the highest priority
        if (sysif_control_abort_set_i) begin
          ctrl_state_d = MbxSysAbortHost;
        end
      end

      // Inbound mailbox being written by the system = writer
      // Outbound mailbox: not applicable
      MbxWrite: begin
        if (hostif_status_error_set_i) begin                 // Host asserts an error
          ctrl_state_d = MbxIdle;
        end else if (sysif_control_abort_set_i) begin         // System wants to abort
          ctrl_state_d = MbxSysAbortHost;
        end else if (writer_close_mbx_i) begin  // Writer decided to close the mailbox
          ctrl_state_d = MbxRead;
        end
      end

      // Inbound mailbox being read by the reader = host
      // Outbound mailbox being read by the reader = system
      MbxRead: begin
        if (hostif_status_error_set_i) begin           // Host asserts an error
          ctrl_state_d = MbxIdle;
        end else if (sysif_control_abort_set_i) begin   // System wants to abort
          ctrl_state_d = MbxSysAbortHost;
        end else if (sys_read_all_i | hostif_status_busy_clear_i) begin
          // Inbound mailbox: Host (FW) finishes the read
          // Outbound mailbox: Object reader (HW) finishes the read
          ctrl_state_d = MbxIdle;
        end
      end

      MbxSysAbortHost: begin
        // Wait for the host to acknowledge the abort
        if (hostif_abort_ack_i) begin
          ctrl_state_d = MbxIdle;
        end
      end

      default: begin
        // Should not reach this
        ctrl_state_d      = MbxIdle;
        mbx_state_error_o = 1'b1;
      end
    endcase
  end
endmodule
