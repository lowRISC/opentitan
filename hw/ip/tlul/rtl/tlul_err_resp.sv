// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// TL-UL error responder module, used by tlul_socket_1n to help response
// to requests to no correct address space. Responses are always one cycle
// after request with no stalling unless response is stuck on the way out.

module tlul_err_resp #(
  // By default, we return a proper bus error. In some cases, we need to return a blank all-zero
  // response without setting the error bit, and for those cases ReturnBlankResp can be set to 1.
  parameter bit ReturnBlankResp = 0
) (
  input                     clk_i,
  input                     rst_ni,
  input  tlul_pkg::tl_h2d_t tl_h_i,
  output tlul_pkg::tl_d2h_t tl_h_o
);
  import tlul_pkg::*;
  import prim_mubi_pkg::*;

  tl_a_op_e                          err_opcode;
  logic [$bits(tl_h_i.a_source)-1:0] err_source;
  logic [$bits(tl_h_i.a_size)-1:0]   err_size;
  logic                              err_rsp_pending;
  mubi4_t                            err_instr_type;
  tlul_pkg::tl_d2h_t                 tl_h_o_int;

  tlul_rsp_intg_gen #(
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(1)
  ) u_intg_gen (
    .tl_i(tl_h_o_int),
    .tl_o(tl_h_o)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      err_rsp_pending <= 1'b0;
      err_source      <= {top_pkg::TL_AIW{1'b0}};
      err_opcode      <= Get;
      err_size        <= '0;
      err_instr_type  <= MuBi4False;
    end else if (err_rsp_pending && tl_h_i.d_ready) begin
      err_rsp_pending <= 1'b0;
    end else if (tl_h_i.a_valid && tl_h_o_int.a_ready) begin
      err_rsp_pending <= 1'b1;
      err_source      <= tl_h_i.a_source;
      err_opcode      <= tl_h_i.a_opcode;
      err_size        <= tl_h_i.a_size;
      err_instr_type  <= tl_h_i.a_user.instr_type;
    end
  end

  assign tl_h_o_int.a_ready  = ~err_rsp_pending;
  assign tl_h_o_int.d_valid  = err_rsp_pending;
  if (ReturnBlankResp) begin : gen_zero_resp
    assign tl_h_o_int.d_data = '0;
  end else begin : gen_err_resp
    assign tl_h_o_int.d_data   = (mubi4_test_true_strict(err_instr_type)) ? DataWhenInstrError :
                                                                            DataWhenError;
  end
  assign tl_h_o_int.d_source = err_source;
  assign tl_h_o_int.d_sink   = '0;
  assign tl_h_o_int.d_param  = '0;
  assign tl_h_o_int.d_size   = err_size;
  assign tl_h_o_int.d_opcode = (err_opcode == Get) ? AccessAckData : AccessAck;
  assign tl_h_o_int.d_user   = '0;
  assign tl_h_o_int.d_error  = ~ReturnBlankResp;

  // Waive unused bits of tl_h_i
  logic unused_tl_h;
  assign unused_tl_h = ^{tl_h_i, err_instr_type};

endmodule
