// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module mbxwrsrm_req_ack (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic req_i,
  input  logic gnt_i,
  output logic tlul_req_o,
  output logic state_error_o
);
  typedef enum logic {
    Idle       = 1'b0,
    WaitForGnt = 1'b1
  } req_state_e;

  req_state_e req_state_d, req_state_q;

  // Following cast is needed to avoid conversion errors between req_state_e <-> logic
  logic [$bits(req_state_e)-1:0] req_state_logic;
  assign req_state_q = req_state_e'(req_state_logic);

  prim_flop #(
    .Width($bits(req_state_e)),
    .ResetValue(Idle)
  ) u_req_state (
    .clk_i ( clk_i           ),
    .rst_ni( rst_ni          ),
    .d_i   ( req_state_d     ),
    .q_o   ( req_state_logic )
  );

  logic wait_for_gnt;
  assign wait_for_gnt = req_state_q == WaitForGnt;

  // Request is leveled and de-asserted when granted
  assign tlul_req_o = (req_i & ~wait_for_gnt) | wait_for_gnt;

  always_comb begin
    req_state_d   = req_state_q;
    state_error_o = 1'b0;

    unique case (req_state_q)
      Idle: begin
        if (req_i & ~gnt_i) begin
          req_state_d = WaitForGnt;
        end
      end

      WaitForGnt: begin
        if (gnt_i) begin
          req_state_d = Idle;
        end
      end

      default: begin
        // Should not reach this
        req_state_d   = Idle;
        state_error_o = 1'b1;
      end
    endcase
  end
endmodule
