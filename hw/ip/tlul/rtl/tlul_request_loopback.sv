// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tlul_request_loopback
  import tlul_pkg::*;
#(
  parameter bit ErrorRsp = 1  // 1: Return TLUL error on on squash
) (
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
  assign loopback_request = tl_h2d_i.a_valid & squash_req_i;

  tlul_pkg::tl_h2d_t tl_muxed_h2d [2];
  tlul_pkg::tl_d2h_t tl_muxed_d2h [2];
  tlul_pkg::tl_h2d_t tl_error_h2d;
  tlul_pkg::tl_d2h_t tl_error_d2h;

  // Device port is Idx0
  assign tl_h2d_o = tl_muxed_h2d[0];
  assign tl_muxed_d2h[0] = tl_d2h_i;

  // Error port is Idx1
  assign tl_error_h2d = tl_muxed_h2d[1];
  assign tl_muxed_d2h[1] = tl_error_d2h;

  // Use a tlul_socket_1n to mux between the genuine response and the error response. The
  // tlul_socket_1n keeps track of outstanding transactions and ensures that all responses
  // happen in the correct order.
  tlul_socket_1n #(
    .N(2),
    .ExplicitErrs(0)
  ) u_socket (
    .clk_i,
    .rst_ni,
    .tl_h_i       (tl_h2d_i),
    .tl_h_o       (tl_d2h_o),
    .tl_d_o       (tl_muxed_h2d),
    .tl_d_i       (tl_muxed_d2h),
    .dev_select_i (loopback_request)
  );

  // Assemble the All-Zero response with error set if the request is squashed
  tlul_pkg::tl_d2h_t tl_razwi_rsp_pre_intg;
  logic loopback_valid_q;

  prim_flop #(
    .Width(1)
  ) u_loopback_valid (
    .clk_i  ( clk_i                ),
    .rst_ni ( rst_ni               ),
    .d_i    ( tl_error_h2d.a_valid ),
    .q_o    ( loopback_valid_q     )
  );

  logic [$bits(tlul_pkg::tl_d_op_e)-1:0] d_opcode_q;
  prim_flop #(
    .Width($bits(tlul_pkg::tl_d_op_e)),
    .ResetValue({AccessAck})
  ) u_rsp_opcode (
    .clk_i  ( clk_i                                                      ),
    .rst_ni ( rst_ni                                                     ),
    .d_i    ( (tl_error_h2d.a_opcode == Get) ? AccessAckData : AccessAck ),
    .q_o    ( d_opcode_q                                                 )
  );
  assign tl_razwi_rsp_pre_intg.d_opcode = tlul_pkg::tl_d_op_e'(d_opcode_q);

  prim_flop #(
    .Width(top_pkg::TL_SZW)
  ) u_rsp_size (
    .clk_i  ( clk_i                        ),
    .rst_ni ( rst_ni                       ),
    .d_i    ( tl_error_h2d.a_size          ),
    .q_o    ( tl_razwi_rsp_pre_intg.d_size )
  );

  prim_flop #(
    .Width(top_pkg::TL_AIW)
  ) u_rsp_source (
    .clk_i  ( clk_i                          ),
    .rst_ni ( rst_ni                         ),
    .d_i    ( tl_error_h2d.a_source          ),
    .q_o    ( tl_razwi_rsp_pre_intg.d_source )
  );

  // Assemble the RAZWI (Return as Zero, Write Ignored) response
  assign tl_razwi_rsp_pre_intg.d_valid = loopback_valid_q;
  assign tl_razwi_rsp_pre_intg.a_ready = 1'b1;

  assign tl_razwi_rsp_pre_intg.d_param = '0;
  assign tl_razwi_rsp_pre_intg.d_sink  = '0;
  assign tl_razwi_rsp_pre_intg.d_data  = '0;
  assign tl_razwi_rsp_pre_intg.d_user  = '0;
  assign tl_razwi_rsp_pre_intg.d_error = ErrorRsp;

  // Compute integrity bits from the manually assembled RAZWI reponse
  tlul_rsp_intg_gen gen_intg_razwi_rsp (
    .tl_i ( tl_razwi_rsp_pre_intg ),
    .tl_o ( tl_error_d2h          )
  );

  // Not all TLUL signals are read from the request muxed to the error leg
  logic unused_tlul_signals;
  assign unused_tlul_signals = ^{tl_error_h2d.a_param,
                                 tl_error_h2d.a_address,
                                 tl_error_h2d.a_mask,
                                 tl_error_h2d.a_data,
                                 tl_error_h2d.a_user,
                                 tl_error_h2d.d_ready};

endmodule
