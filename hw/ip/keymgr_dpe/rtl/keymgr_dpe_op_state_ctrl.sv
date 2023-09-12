// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager operation state control
//

`include "prim_assert.sv"

module keymgr_dpe_op_state_ctrl
  import keymgr_dpe_pkg::*;
  import keymgr_dpe_reg_pkg::*;
(
  input clk_i,
  input rst_ni,

  input adv_req_i,
  input gen_req_i,
  input erase_req_i,

  // `op_ack_o` signals to the top module that the requested operation is completed
  output logic op_ack_o,
  output logic op_busy_o,
  // `op_update_o` signals to the keygmr slot MUX that destination slot needs to be updated
  output logic op_update_o,

  input kmac_done_i,
  output logic adv_en_o,
  output logic gen_en_o,

  output logic op_fsm_err_o

);

  localparam int OpStateWidth = 8;
  typedef enum logic [OpStateWidth-1:0] {
    StIdle   = 8'b10010101,
    StAdv    = 8'b00101000,
    StErase  = 8'b01000011,
    StWait   = 8'b11111110
  } state_e;

  state_e state_q, state_d;
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StIdle)

  logic gen_en;
  assign gen_en_o = gen_en & gen_req_i;

  always_comb begin
    state_d = state_q;
    op_update_o = 1'b0;
    op_ack_o = 1'b0;
    op_busy_o = 1'b0;

    // output to kmac interface
    adv_en_o = 1'b0;

    gen_en = 1'b0;
    op_fsm_err_o = 1'b0;

    unique case (state_q)
      StIdle: begin
        if (adv_req_i) begin
          state_d = StAdv;
        end else if (gen_req_i) begin
          state_d = StWait;
        end else if (erase_req_i) begin
          state_d = StErase;
        end
      end

      // Erasing happens in a single clock cycle in keymgr slot MUX of ctrl, therefore:
      // `op_update_o` signal is used as input to MUX (so that MUX is activated to update the slot)
      // `op_ack_o` signal is used to communicate successful completion of command
      StErase:begin
        op_ack_o = 1'b1;
        op_update_o = 1'b1;
        state_d = StIdle;
      end

      StAdv: begin
        adv_en_o = 1'b1;
        op_busy_o = 1'b1;

        if (kmac_done_i) begin
          op_ack_o = 1'b1;
          op_update_o = 1'b1;
          state_d = StIdle;
        end
      end

      // Not an advanced operation
      StWait: begin
        gen_en = 1'b1;
        op_busy_o = 1'b1;

        if (kmac_done_i) begin
          op_ack_o = 1'b1;
          state_d = StIdle;
        end
      end

      // error state
      default: begin
        // allow completion of transaction
        op_ack_o = 1'b1;
        op_fsm_err_o = 1'b1;
        op_busy_o = 1'b1;
      end

    endcase // unique case (adv_state_q)
  end


endmodule // keymgr_dpe_op_state_ctrl
