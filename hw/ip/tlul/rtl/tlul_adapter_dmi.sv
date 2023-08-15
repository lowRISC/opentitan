// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Tile-Link UL adapter for RISC-V debug module from the PULP project.
//
// Note that this module can only handle one outstanding request at a time.

`include "prim_assert.sv"

module tlul_adapter_dmi
  import tlul_pkg::*;
#(
  parameter  bit CmdIntgCheck      = 1,  // 1: Enable command integrity check
  parameter  bit EnableRspIntgGen  = 1,  // 1: Generate response integrity
  parameter  bit EnableDataIntgGen = 1,  // 1: Generate response data integrity
  // This is fixed by the dm_pkg.
  // Unfortunately there only exists a request struct type, hence these
  // values have to be hardcoded here. Two SVAs are added further below to make
  // sure these are aligned with the widths in dm_pkg.
  localparam int DmiAw             = 7,  // Width of register address
  localparam int DmiDw             = 32  // Shall be matched with TL_DW
) (
  input clk_i,
  input rst_ni,

  // TL-UL interface
  input  tl_h2d_t tl_h2d_i,
  output tl_d2h_t tl_d2h_o,

  // control interface
  output logic    intg_error_o,

  output logic          dmi_req_valid_o,
  input  logic          dmi_req_ready_i,
  output dm::dmi_req_t  dmi_req_o,

  input  logic          dmi_resp_valid_i,
  output logic          dmi_resp_ready_o,
  input  dm::dmi_resp_t dmi_resp_i
);

  localparam int IdW = $bits(tl_h2d_i.a_source);
  localparam int SzW = $bits(tl_h2d_i.a_size);

  logic a_ack, d_ack;  // Indicates whether the corresponding valid/ready handshake completes.
  logic outstanding_q; // Indicates whether there is a pending request.
  assign a_ack   = tl_h2d_i.a_valid & tl_d2h_o.a_ready;
  assign d_ack   = tl_d2h_o.d_valid & tl_h2d_i.d_ready;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)    outstanding_q <= 1'b0;
    else if (a_ack) outstanding_q <= 1'b1;
    else if (d_ack) outstanding_q <= 1'b0;
  end

  // Decode Requests
  logic rd_req, wr_req;
  assign wr_req  = tl_h2d_i.a_valid && ((tl_h2d_i.a_opcode == PutFullData) ||
                                        (tl_h2d_i.a_opcode == PutPartialData));
  assign rd_req  = tl_h2d_i.a_valid && (tl_h2d_i.a_opcode == Get);

  // If we detect an error, the response will be returned immediately in the next cycle
  // and we do not send a request out to the DMI.
  logic error_d, error_q;
  assign dmi_req_valid_o = (wr_req || rd_req) && !error_d;
  // The DMI response can be accepted if there is a pending request without error.
  assign dmi_resp_ready_o = outstanding_q && !error_q;

  // We expect a word-aligned address here, otherwise an error is returned (see further below).
  assign dmi_req_o.addr = tl_h2d_i.a_address[DmiAw+2-1:2];
  assign dmi_req_o.data = tl_h2d_i.a_data;
  assign dmi_req_o.op   = (wr_req) ? dm::DTM_WRITE :
                          (rd_req) ? dm::DTM_READ  : dm::DTM_NOP;

  logic [IdW-1:0] reqid_q;
  logic [SzW-1:0] reqsz_q;
  tl_d_op_e       rspop_q;
  logic wr_req_q, rd_req_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reqid_q  <= '0;
      reqsz_q  <= '0;
      rspop_q  <= AccessAck;
      error_q  <= 1'b0;
      wr_req_q <= 1'b0;
      rd_req_q <= 1'b0;
    end else if (a_ack) begin
      reqid_q <= tl_h2d_i.a_source;
      reqsz_q <= tl_h2d_i.a_size;
      // Return AccessAckData regardless of error
      rspop_q <= (rd_req) ? AccessAckData : AccessAck;
      rd_req_q <= rd_req;
      wr_req_q <= wr_req;
      error_q  <= error_d;
    end
  end

  // Send back a bus error if the dm_csrs module responded with an error.
  logic error_resp;
  assign error_resp = error_q || (dmi_resp_i.resp == dm::DTM_ERR);

  tlul_pkg::tl_d2h_t tl_d2h_o_pre;
  assign tl_d2h_o_pre = '{
    // We are ready to accept a request if there is no outstanding one and if the DMI is ready.
    a_ready:  dmi_req_ready_i && !outstanding_q,
    // A data response is valid if the DMI response is valid and we've got an outstanding request.
    // If the request resulted in an internal error, the error response is returned without a DMI
    // response, since the request to the DMI has been suppressed by the error.
    d_valid:  (dmi_resp_valid_i || error_q) && outstanding_q,
    d_opcode: rspop_q,
    d_param:  '0,
    d_size:   reqsz_q,
    d_source: reqid_q,
    d_sink:   '0,
    // Blank data upon error in the same way as other TL-UL adapters would in OpenTitan.
    d_data:   (rd_req_q && !(error_resp || wr_req_q)) ? dmi_resp_i.data : {DmiDw{1'b1}},
    d_user:   '0,
    d_error:  error_resp
  };

  // outgoing integrity generation
  tlul_rsp_intg_gen #(
    .EnableRspIntgGen(EnableRspIntgGen),
    .EnableDataIntgGen(EnableDataIntgGen)
  ) u_rsp_intg_gen (
    .tl_i(tl_d2h_o_pre),
    .tl_o(tl_d2h_o)
  );

  logic intg_error;
  if (CmdIntgCheck) begin : gen_cmd_intg_check
    logic intg_error_q;
    tlul_cmd_intg_chk u_cmd_intg_chk (
      .tl_i(tl_h2d_i),
      .err_o(intg_error)
    );
    // permanently latch integrity error until reset
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        intg_error_q <= 1'b0;
      end else if (intg_error) begin
        intg_error_q <= 1'b1;
      end
    end
    assign intg_error_o = intg_error_q;
  end else begin : gen_no_cmd_intg_check
    assign intg_error = 1'b0;
    assign intg_error_o = 1'b0;
  end

  ////////////////////
  // Error Handling //
  ////////////////////

  logic addr_oob_err;       // Address out of bounds error.
  logic addr_align_err;     // Size and alignment
  logic malformed_meta_err; // User signal format error or unsupported
  logic tl_err;             // Common TL-UL error checker
  assign error_d = addr_oob_err ||
                   addr_align_err ||
                   malformed_meta_err ||
                   tl_err ||
                   intg_error;

  // Error if the address is larger than what can be represented with DmiAw
  assign addr_oob_err = (wr_req || rd_req) && |(tl_h2d_i.a_address >> (2 + DmiAw));

  // addr_align_err
  //    Raised if addr isn't aligned with the size
  //    Read size error is checked in tlul_assert.sv
  //    Here is it added due to the limitation of register interface.
  //    Only word-align is accepted based on comportability spec.
  assign addr_align_err = (wr_req) && |tl_h2d_i.a_address[1:0];

  // Don't allow unsupported values.
  assign malformed_meta_err = tl_a_user_chk(tl_h2d_i.a_user);

  // tl_err : separate checker
  tlul_err u_err (
    .clk_i,
    .rst_ni,
    .tl_i(tl_h2d_i),
    .err_o (tl_err)
  );

  `ASSERT_INIT(DwMatchedWithTl_A, DmiDw == top_pkg::TL_DW)
  `ASSERT_INIT(DwMatchedWithDm_A, DmiDw == $bits(dmi_req_o.data))
  `ASSERT_INIT(AwIsMatchedWithDm, DmiAw == $bits(dmi_req_o.addr))

endmodule : tlul_adapter_dmi
