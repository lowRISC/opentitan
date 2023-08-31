// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager operation state control
//

`include "prim_assert.sv"

module keymgr_op_state_ctrl
  import keymgr_pkg::*;
  import keymgr_reg_pkg::*;
(
  input clk_i,
  input rst_ni,

  input adv_req_i,
  input dis_req_i,
  input id_req_i,
  input gen_req_i,
  input [CdiWidth-1:0] cnt_i,
  output logic op_ack_o,
  output logic op_busy_o,
  output logic op_update_o,

  input kmac_done_i,
  output logic adv_en_o,
  output logic id_en_o,
  output logic gen_en_o,

  output logic op_fsm_err_o

);

  localparam int OpStateWidth = 8;
  typedef enum logic [OpStateWidth-1:0] {
    StIdle   = 8'b10010101,
    StAdv    = 8'b00101000,
    StAdvAck = 8'b01000011,
    StWait   = 8'b11111110
  } state_e;

  state_e state_q, state_d;
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StIdle)

  logic gen_en;
  assign id_en_o = gen_en & id_req_i;
  assign gen_en_o = gen_en & gen_req_i;

  always_comb begin
    state_d = state_q;
    op_update_o = 1'b0;
    op_ack_o = 1'b0;
    op_busy_o = 1'b1;

    // output to kmac interface
    adv_en_o = 1'b0;

    gen_en = 1'b0;
    op_fsm_err_o = 1'b0;

    unique case (state_q)
      StIdle: begin
        op_busy_o = '0;
        if (adv_req_i || dis_req_i) begin
          state_d = StAdv;
        end else if (id_req_i || gen_req_i) begin
          state_d = StWait;
        end
      end

      StAdv: begin
        adv_en_o = 1'b1;

        if (kmac_done_i && (int'(cnt_i) == CDIs-1)) begin
          op_ack_o = 1'b1;
          state_d = StIdle;
        end else if (kmac_done_i && (int'(cnt_i) < CDIs-1)) begin
          op_update_o = 1'b1;
          state_d = StAdvAck;
        end
      end

      // drop adv_en_o to allow kmac interface handshake
      StAdvAck: begin
        state_d = StAdv;
      end

      // Not an advanced operation
      StWait: begin
        gen_en = 1'b1;

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
      end

    endcase // unique case (adv_state_q)
  end


endmodule // keymgr_op_state_ctrl
