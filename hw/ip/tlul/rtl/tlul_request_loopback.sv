// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tlul_request_loopback
  import tlul_pkg::*;
(
  input  logic              clk_i,
  input  logic              rst_ni,
  input  logic              squash_req_i,
  input  tlul_pkg::tl_h2d_t tl_h2d_i,   // Incoming request
  output tlul_pkg::tl_d2h_t tl_d2h_o,   // Response
  output tlul_pkg::tl_h2d_t tl_h2d_o,   // Feed through request if not squashed to the target
  input  tlul_pkg::tl_d2h_t tl_d2h_i    // Response from the target
);

  // A valid request is looped back if the squash_req_i is asserted in the same cycle
  // Regardless of the request being squashed or not, the request payload is NOT modified by this
  // module
  logic loopback_request;
  assign  loopback_request = tl_h2d_i.a_valid & squash_req_i;

  // Assemble the non-squashed request
  always_comb begin
    tl_h2d_o         = tl_h2d_i;
    tl_h2d_o.a_valid = tl_h2d_i.a_valid & ~squash_req_i;
  end

  // Assemble the All-Zero response with error set if the request is squashed
  tlul_pkg::tl_d2h_t tl_razwi_rsp_pre_intg, tl_razwi_rsp;
  logic loopback_request_q;

  prim_flop #(
    .Width(1)
  ) u_loopback_valid (
    .clk_i  ( clk_i              ),
    .rst_ni ( rst_ni             ),
    .d_i    ( loopback_request   ),
    .q_o    ( loopback_request_q )
  );

  prim_flop #(
    .Width($bits(tlul_pkg::tl_d_op_e)),
    .ResetValue({AccessAck})
  ) u_rsp_opcode (
    .clk_i  ( clk_i                                                  ),
    .rst_ni ( rst_ni                                                 ),
    .d_i    ( (tl_h2d_i.a_opcode == Get) ? AccessAckData : AccessAck ),
    .q_o    ( tl_razwi_rsp_pre_intg.d_opcode                         )
  );

  prim_flop #(
    .Width(top_pkg::TL_SZW)
  ) u_rsp_size (
    .clk_i  ( clk_i                        ),
    .rst_ni ( rst_ni                       ),
    .d_i    ( tl_h2d_i.a_size              ),
    .q_o    ( tl_razwi_rsp_pre_intg.d_size )
  );

  prim_flop #(
    .Width(top_pkg::TL_AIW)
  ) u_rsp_source (
    .clk_i  ( clk_i                          ),
    .rst_ni ( rst_ni                         ),
    .d_i    ( tl_h2d_i.a_source              ),
    .q_o    ( tl_razwi_rsp_pre_intg.d_source )
  );

  // Assemble the RAZWI (Return as Zero, Write Ignored) response
  assign tl_razwi_rsp_pre_intg.d_valid = loopback_request_q;
  assign tl_razwi_rsp_pre_intg.a_ready = 1'b1;

  assign tl_razwi_rsp_pre_intg.d_param = '0;
  assign tl_razwi_rsp_pre_intg.d_sink  = '0;
  assign tl_razwi_rsp_pre_intg.d_data  = '0;
  assign tl_razwi_rsp_pre_intg.d_user  = '0;
  assign tl_razwi_rsp_pre_intg.d_error = 1'b1;

  // Compute integrity bits from the manually assembled RAZWI reponse
  tlul_rsp_intg_gen gen_intg_razwi_rsp (
    .tl_i ( tl_razwi_rsp_pre_intg ),
    .tl_o ( tl_razwi_rsp          )
  );

  // Mux reponse if request was squased
  assign tl_d2h_o = loopback_request_q ? tl_razwi_rsp : tl_d2h_i;

endmodule
