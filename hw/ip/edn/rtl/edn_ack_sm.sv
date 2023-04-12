// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: interface between a req/ack interface and a fifo
//

module edn_ack_sm (
  input logic                clk_i,
  input logic                rst_ni,

  input logic                enable_i,
  input logic                req_i,
  output logic               ack_o,
  input logic                local_escalate_i,
  input logic                fifo_not_empty_i,
  output logic               fifo_pop_o,
  output logic               fifo_clr_o,
  output logic               ack_sm_err_o
);

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 4 -n 6 \
  //      -s 2299232677 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (50.00%)
  //  4: ||||||||||||| (33.33%)
  //  5: |||||| (16.67%)
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 5
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 4
  //
  localparam int StateWidth = 9;
  typedef enum logic [StateWidth-1:0] {
    Disabled      = 9'b100110010, // Disabled
    EndPointClear = 9'b110001110, // Clear out end point before beginning
    Idle          = 9'b001011100, // idle (hamming distance = 3)
    DataWait      = 9'b011101011, // wait for data to return
    AckPls        = 9'b000100101, // signal ack to endpoint
    Error         = 9'b111010001  // illegal state reached and hang
  } state_e;
  state_e state_d, state_q;

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, Disabled)

  always_comb begin
    state_d      = state_q;
    ack_o        = 1'b0;
    fifo_clr_o   = 1'b0;
    fifo_pop_o   = 1'b0;
    ack_sm_err_o = 1'b0;
    unique case (state_q)
      Disabled: begin
        if (enable_i) begin
          state_d = EndPointClear;
          fifo_clr_o = 1'b1;
        end
      end
      EndPointClear: begin
        state_d = Idle;
      end
      Idle: begin
        if (req_i) begin
          if (fifo_not_empty_i) begin
            fifo_pop_o = 1'b1;
          end
          state_d = DataWait;
        end
      end
      DataWait: begin
        if (fifo_not_empty_i) begin
          state_d = AckPls;
        end
      end
      AckPls: begin
        ack_o = 1'b1;
        state_d = Idle;
      end
      Error: begin
        ack_sm_err_o = 1'b1;
      end
      default: begin
        ack_sm_err_o = 1'b1;
        state_d = Error;
      end
    endcase // unique case (state_q)

    // If local escalation is seen, transition directly to
    // error state.
    if (local_escalate_i) begin
      state_d = Error;
      // Tie off outputs, except for ack_sm_err_o.
      ack_o      = 1'b0;
      fifo_clr_o = 1'b0;
      fifo_pop_o = 1'b0;
    end else if (!enable_i && state_q inside {EndPointClear, Idle, DataWait, AckPls}) begin
      // Only disable if state is legal and not Disabled or Error.
      // Even when disabled, illegal states must result in a transition to Error.
      state_d = Disabled;
      // Tie off all outputs, except for ack_sm_err_o.
      ack_o        = 1'b0;
      fifo_pop_o   = 1'b0;
      fifo_clr_o   = 1'b0;
    end
  end

  // The `local_escalate_i` includes `ack_sm_err_o`.
  // The following assertion ensures the Error state is stable until reset.
  // With `FpvSecCm` prefix, this assertion will added to weekly FPV sec_cm regression.
  `ASSERT(FpvSecCmErrorStEscalate_A, state_q == Error |-> local_escalate_i)

  // This assertion does not have `FpvSecCm` prefix because the sec_cm FPV environment will
  // blackbox the `prim_sparse_fsm` `state_q` output.
  `ASSERT(AckSmErrorStStable_A,   state_q == Error |=> $stable(state_q))

endmodule
