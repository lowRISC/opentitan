// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Phy Erase Module
// Translates the controller's req/ack interface to the interface expected by the flash wrapper
// Longer term the controller protocol can be changed to match.

module flash_phy_erase import flash_phy_pkg::*; (
  input clk_i,
  input rst_ni,

  // interface with controller
  input pg_erase_req_i,
  input bk_erase_req_i,
  input suspend_req_i,
  output logic ack_o,

  // interface with flash
  output logic pg_erase_req_o,
  output logic bk_erase_req_o,
  output logic suspend_req_o,
  input ack_i,
  input done_i
);

  typedef enum logic [1:0] {
    StEraseIdle,
    StEraseBusy,
    StEraseSuspend
  } erase_state_e;

  erase_state_e state_d, state_q;

  logic req_valid;
  logic suspend_valid;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StEraseIdle;
    end else begin
      state_q <= state_d;
    end
  end

  always_comb begin
    req_valid = 1'b0;
    suspend_valid = 1'b0;
    ack_o = 1'b0;
    state_d = state_q;

    unique case (state_q)
      StEraseIdle: begin
        req_valid = 1'b1;

        if ((pg_erase_req_o || bk_erase_req_o) && ack_i) begin
          state_d = StEraseBusy;
        end
      end

      StEraseBusy: begin
        suspend_valid = '1;

        if (suspend_req_i && ack_i) begin
          state_d = StEraseSuspend;
        end else if (done_i) begin
          ack_o = 1'b1;
          state_d = StEraseIdle;
        end
      end

      StEraseSuspend: begin
        if (done_i) begin
          ack_o = 1'b1;
          state_d = StEraseIdle;
        end
      end

      default:;
    endcase // unique case (state_q)
  end

  assign pg_erase_req_o = pg_erase_req_i & req_valid;
  assign bk_erase_req_o = bk_erase_req_i & req_valid;
  assign suspend_req_o = suspend_req_i & suspend_valid;

endmodule
