// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

// Tile-Link UL to register interface adapter
//
// This module acts as a device, addressed through the TL-UL bus. It receives Get, PutPartialData
// and PutFullData messages on the A channel. These are read or write requests, which are passed to
// the register interface on the same cycle. The response from the register interface is sent back
// to the host as a message on the D channel on the next cycle.
//
// A module instance performs several checks on A-channel messages and only forwards a request to
// the register interface if they all pass. These checks are:
//
//  - A_OPCODE must be Get, PutPartialData or PutFullData.
//
//  - A_SIZE must be 0, 1 or 2 (giving a 1-, 2- or 4-byte operation, respectively).
//
//  - A_ADDRESS must be naturally aligned for the operation byte width signaled in A_SIZE.
//
//  - A_MASK must only be true for active byte-lanes. The position of the first of these active
//    lanes is calculated from the address, modulo the width of the TL-UL data bus.
//
//  - If the A_USER.INSTR_TYPE value is MuBi4True, A_OPCODE must be Get.
//
//  - Either the A_USER.INSTR_TYPE value must be a value other than MuBi4True or the en_ifetch_i
//    port must be MuBi4True.
//
//  - If the CmdIntgCheck parameter is true then the command integrity check must pass.
//
//
// ** Parameters
//
// CmdIntgCheck: If this parameter is true then there is a "command integrity check". This uses a
//               tlul_cmd_intg_chk instance to compare integrity checksums from requests on the A
//               channel. If the integrity checksums don't match, the adapter doesn't pass the
//               request to the register interface through re_o/we_o and the response on the D
//               channel will then have its D_ERROR flag set.
//
// EnableRspIntgGen: OpenTitan sends response integrity with messages on the TL-UL bus. If this
//                   parameter is true, the module will perform calculations to send a correct
//                   integrity value in the response's A_USER.RSP_INTG field.
//
// EnableDataIntgGen: This parameter is analogous to EnableRspIntgGen but controls whether the
//                    module performs calculations to send a correct integrity value in the
//                    response's A_USER.DATA_INTG field.
//
// RegAw: The number of bits used for addresses in the register interface. Higher bits of the
//        A_ADDRESS field in an A channel message are ignored.
//
// RegDw: The number of bits used for data words in the register interface. This is assumed to match
//        the data width of the TL-UL bus (see the MatchedWidth_A assertion).
//
// AccessLatency: This adapter always returns TileLink responses after one cycle, but this parameter
//                allows it to handle different timings on the register interface. If AccessLatency
//                is zero then the adapter expects a combinatorial response on the register
//                interface and flops the result to break paths and add a cycle delay. If
//                AccessLatency is one then the adapter expects a response on the register interface
//                in the cycle after the re_o/we_o signal goes high, but then forwards it
//                combinatorially to the TileLink interface. Only values 0 and 1 are allowed for
//                this parameter.
//
//
// ** Ports
//
// clk_i/rst_ni: Clock and reset.
// tl_i/tl_o:    Connections to the TL-UL bus.
// en_ifetch_i:  This mubi4_t port controls whether to allow read requests from Get messages whose
//               A_USER.INSTR_TYPE is MuBi4True (considered to be processor "fetch" requests).
// intg_error_o: This port is high when the adapter has detected a command integrity error. That can
//               only happen if the CmdIntgCheck parameter is set.
// re_o/we_o:    The read-enable and write-enable ports in the register interface.
// addr_o:       The address to read or write through the register interface.
// wdata_o:      The value to write through the register interface if we_o is true.
// be_o:         A byte-enable signal, which is true for each byte-lane where the TL-UL operation's
//               mask is true.
// busy_i:       If this input is high then the A channel interface is stalled (by dropping
//               A_READY), which means that the adapter will not accept any new operations.
// rdata_i:      Read data being returned for a read request through the register interface.
// error_i:      An error flag in the register interface. This signals that an error has been seen,
//               which can be seen in the D channel response by D_ERROR being high. The D_DATA
//               response is also set to '1, squashing any data that might have been returned
//               through rdata_i.
//
// ICEBOX(#15822): Note that due to some modules with special needs (like the vendored-in RV_DM),
//                 this module has been extended so that it supports use cases outside of the
//                 generated reg_top module. This makes this adapter and its parameterization
//                 options a bit heavy.
//
//                 We should in the future come back to this and refactor / align the module and its
//                 parameterization needs.

module tlul_adapter_reg
  import tlul_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter  bit CmdIntgCheck      = 0,  // 1: Enable command integrity check
  parameter  bit EnableRspIntgGen  = 0,  // 1: Generate response integrity
  parameter  bit EnableDataIntgGen = 0,  // 1: Generate response data integrity
  parameter  int RegAw             = 8,  // Width of register address
  parameter  int RegDw             = 32, // Shall be matched with TL_DW
  parameter  int AccessLatency     = 0,  // 0: same cycle, 1: next cycle
  localparam int RegBw             = RegDw/8
) (
  input clk_i,
  input rst_ni,

  // TL-UL interface
  input  tl_h2d_t tl_i,
  output tl_d2h_t tl_o,

  // control interface
  input  mubi4_t  en_ifetch_i,
  output logic    intg_error_o,

  // Register interface
  output logic             re_o,
  output logic             we_o,
  output logic [RegAw-1:0] addr_o,
  output logic [RegDw-1:0] wdata_o,
  output logic [RegBw-1:0] be_o,
  input                    busy_i,
  // The following two signals are expected
  // to be returned in AccessLatency cycles.
  input        [RegDw-1:0] rdata_i,
  // This can be a write or read error.
  input                    error_i
);

  `ASSERT_INIT(AllowedLatency_A, AccessLatency inside {0, 1})

  localparam int IW  = $bits(tl_i.a_source);
  localparam int SZW = $bits(tl_i.a_size);

  logic outstanding_q;    // Indicates current request is pending
  logic a_ack, d_ack;

  logic [RegDw-1:0] rdata, rdata_q;
  logic             error_q, error, err_internal, instr_error, intg_error;

  logic addr_align_err;     // Size and alignment
  logic tl_err;             // Common TL-UL error checker

  logic [IW-1:0]  reqid_q;
  logic [SZW-1:0] reqsz_q;
  tl_d_op_e       rspop_q;

  logic rd_req, wr_req;

  assign a_ack   = tl_i.a_valid & tl_o.a_ready;
  assign d_ack   = tl_o.d_valid & tl_i.d_ready;
  // Request signal
  assign wr_req  = a_ack & ((tl_i.a_opcode == PutFullData) | (tl_i.a_opcode == PutPartialData));
  assign rd_req  = a_ack & (tl_i.a_opcode == Get);

  assign we_o    = wr_req & ~err_internal;
  assign re_o    = rd_req & ~err_internal;
  assign wdata_o = tl_i.a_data;
  assign be_o    = tl_i.a_mask;

  if (RegAw <= 2) begin : gen_only_one_reg
    assign addr_o  = '0;
  end else begin : gen_more_regs
    assign addr_o  = {tl_i.a_address[RegAw-1:2], 2'b00}; // generate always word-align
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)    outstanding_q <= 1'b0;
    else if (a_ack) outstanding_q <= 1'b1;
    else if (d_ack) outstanding_q <= 1'b0;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reqid_q <= '0;
      reqsz_q <= '0;
      rspop_q <= AccessAck;
    end else if (a_ack) begin
      reqid_q <= tl_i.a_source;
      reqsz_q <= tl_i.a_size;
      // Return AccessAckData regardless of error
      rspop_q <= (rd_req) ? AccessAckData : AccessAck ;
    end
  end

  if (AccessLatency == 1) begin : gen_access_latency1
    logic a_ack_q, err_internal_q, wr_req_q;
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        a_ack_q <= 1'b0;
        err_internal_q <= 1'b0;
        wr_req_q <= 1'b0;
        rdata_q  <= '0;
        error_q  <= 1'b0;
      end else begin
        a_ack_q <= a_ack;
        err_internal_q <= err_internal;
        wr_req_q <= wr_req;

        rdata_q  <= rdata;
        error_q  <= error;
      end
    end
    always_comb begin
      if (a_ack_q) begin
        rdata = (error_i || err_internal_q || wr_req_q) ? '1 : rdata_i;
        error = error_i || err_internal_q;
      end else begin
        rdata = rdata_q;
        error = error_q;
      end
    end
  end else begin : gen_access_latency0
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rdata_q <= '0;
        error_q <= 1'b0;
      end else if (a_ack) begin
        rdata_q <= (error_i || err_internal || wr_req) ? '1 : rdata_i;
        error_q <= error_i || err_internal;
      end
    end
    assign rdata = rdata_q;
    assign error = error_q;
  end

  tlul_pkg::tl_d2h_t tl_o_pre;
  assign tl_o_pre = '{
    a_ready:  ~(outstanding_q | busy_i),
    d_valid:  outstanding_q,
    d_opcode: rspop_q,
    d_param:  '0,
    d_size:   reqsz_q,
    d_source: reqid_q,
    d_sink:   '0,
    d_data:   rdata,
    d_user:   '0,
    d_error:  error
  };

  // outgoing integrity generation
  tlul_rsp_intg_gen #(
    .EnableRspIntgGen(EnableRspIntgGen),
    .EnableDataIntgGen(EnableDataIntgGen),
    .UserInIsZero(1'b1)
  ) u_rsp_intg_gen (
    .tl_i(tl_o_pre),
    .tl_o(tl_o)
  );

  if (CmdIntgCheck) begin : gen_cmd_intg_check
    logic intg_error_q;
    tlul_cmd_intg_chk u_cmd_intg_chk (
      .tl_i(tl_i),
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

  // An instruction type transaction is only valid if en_ifetch is enabled
  assign instr_error = prim_mubi_pkg::mubi4_test_true_strict(tl_i.a_user.instr_type) &
                       prim_mubi_pkg::mubi4_test_false_loose(en_ifetch_i);

  assign err_internal = addr_align_err | tl_err | instr_error | intg_error;

  // addr_align_err
  //    Raised if addr isn't aligned with the size
  //    Read size error is checked in tlul_assert.sv
  //    Here is it added due to the limitation of register interface.
  always_comb begin
    if (wr_req) begin
      // Only word-align is accepted based on comportability spec
      addr_align_err = |tl_i.a_address[1:0];
    end else begin
      // No request
      addr_align_err = 1'b0;
    end
  end

  // tl_err : separate checker
  tlul_err u_err (
    .clk_i,
    .rst_ni,
    .tl_i,
    .err_o (tl_err)
  );

  `ASSERT_INIT(MatchedWidth_A, RegDw == top_pkg::TL_DW)

endmodule
