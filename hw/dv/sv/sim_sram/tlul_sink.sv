// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Provides termination for a TL interface.
module tlul_sink #(
    parameter bit SameCycleResp = 1'b1
) (
    input clk_i,
    input rst_ni,

    input  tlul_pkg::tl_h2d_t tl_i,
    output tlul_pkg::tl_d2h_t tl_o
);

  tlul_pkg::tl_h2d_t tl_i_q;

  if (SameCycleResp) begin : gen_same_cycle_resp

    assign tl_i_q = tl_i;

  end : gen_same_cycle_resp
  else begin : gen_next_cycle_resp

    // Delay the req by one cycle, have d_valid follow a_valid.
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        tl_i_q <= tlul_pkg::TL_H2D_DEFAULT;
      end else begin
        tl_i_q <= tl_i;
      end
    end

  end : gen_next_cycle_resp

  assign tl_o = '{
    d_valid  : tl_i_q.a_valid,
    d_opcode : (tl_i_q.a_valid && tl_i_q.a_opcode == tlul_pkg::Get) ? tlul_pkg::AccessAckData :
                                                                      tlul_pkg::AccessAck,
    d_param  : '0,
    d_size   : (tl_i_q.a_valid) ? tl_i_q.a_size : '0,
    d_source : (tl_i_q.a_valid) ? tl_i_q.a_source : '0,
    d_sink   : '0,
    d_data   : '0,
    d_user   : '0,
    d_error  : 1'b0,
    a_ready  : 1'b1
  };

endmodule
