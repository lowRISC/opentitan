// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: interface between a req/ack interface and a fifo
//

module entropy_src_ack_sm (
  input logic                clk_i,
  input logic                rst_ni,

  input logic                enable_i,
  input logic                req_i,
  output logic               ack_o,
  input logic                fifo_not_empty_i,
  input logic                local_escalate_i,
  output logic               fifo_pop_o,
  output logic               ack_sm_err_o
);

  import entropy_src_ack_sm_pkg::*;

  state_e state_d, state_q;

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, Idle)

  always_comb begin
    state_d = state_q;
    ack_o = 1'b0;
    fifo_pop_o = 1'b0;
    ack_sm_err_o = 1'b0;
    unique case (state_q)
      Idle: begin
        if (enable_i) begin
          if (req_i) begin
            state_d = Wait;
          end
        end
      end
      Wait: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (fifo_not_empty_i) begin
            ack_o = 1'b1;
            fifo_pop_o = 1'b1;
            state_d = Idle;
          end
        end
      end
      Error: begin
        ack_sm_err_o = 1'b1;
      end
      default: begin
        state_d = Error;
        ack_sm_err_o = 1'b1;
      end
    endcase
    if (local_escalate_i) begin
      state_d = Error;
    end
  end

endmodule
