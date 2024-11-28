// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Adapter that translates generic read/write requests into valid TLUL equivalents.

`include "prim_assert.sv"

module tlul_adapter_tb_reqs
  import tlul_pkg::*;
#(
  parameter bit EnableDataIntgGen = 1,
  parameter bit EnableRspDataIntgCheck = 1
) (
  input clk_i,
  input rst_ni,

  output tl_h2d_t tl_o,
  input  tl_d2h_t tl_i,

  // A valid request is indicated with `en_i` and is acknowledged once `wait_o` is unset.
  input  logic en_i,
  output logic wait_o,

  // Generic read/write request.
  input  logic [top_pkg::TL_AW-1:0] addr_i,
  input  logic                      write_i,
  input  logic [top_pkg::TL_DW-1:0] wdata_i,
  output logic [top_pkg::TL_DW-1:0] rdata_o,
  output logic                      error_o
);

  // Differentiate between two levels of acknowledgements:
  //  - `req_ack`: A host-to-device request is acknowledged by the device,
  //     meaning that the response is pending.
  //  - `resp_ack`: The device-to-host response is acknowledged.
  logic pending_d, pending_q;
  logic req_ack, resp_ack;

  assign req_ack =  en_i & tl_i.a_ready & tl_o.a_valid;
  assign resp_ack = en_i & tl_o.d_ready & tl_i.d_valid;

  assign pending_d = req_ack  ? 1'b1 :
                     resp_ack ? 1'b0 : pending_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pending_q <= 1'b0;
    end else begin
      pending_q <= pending_d;
    end
  end

  // Only make a new request (through `a_valid`) to the device when none are pending. If the
  // integrity checks are enabled, the `a_user` fields will be set by the corresponding module
  // (see `tlul_cmd_intg_gen`).
  tlul_pkg::tl_h2d_t tl_o_pre;
  assign tl_o_pre = '{
    a_valid: en_i & ~pending_q,
    a_opcode: ~write_i ? Get : PutFullData,
    a_size: 2'b10,
    a_mask: 4'b1111,
    a_source: '0,
    a_address:addr_i,
    a_data: wdata_i,
    a_user: TL_A_USER_DEFAULT,
    d_ready: 1'b1,
    a_param: 3'h0
  };

  assign wait_o  = pending_q && tl_o.d_ready && tl_i.d_valid ? 1'b0 : 1'b1;
  assign rdata_o = tl_i.d_data;
  assign error_o = tl_i.d_error | intg_err_chk;

  tlul_cmd_intg_gen #(
    .EnableDataIntgGen (EnableDataIntgGen)
  ) u_cmd_intg_gen (
    .tl_i ( tl_o_pre ),
    .tl_o ( tl_o     )
  );

  logic intg_err_chk;
  tlul_rsp_intg_chk #(
    .EnableRspDataIntgCheck(EnableRspDataIntgCheck)
  ) u_rsp_chk (
    .tl_i  ( tl_i         ),
    .err_o ( intg_err_chk )
  );

endmodule
