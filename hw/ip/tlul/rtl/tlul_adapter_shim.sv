// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module tlul_adapter_shim
  import tlul_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter bit [31:0] SHIM_NAME_0 = 32'hDEADBEEF,
  parameter bit [31:0] SHIM_NAME_1 = 32'hCAFEBABE,
  parameter bit [31:0] SHIM_VERSION_0 = 32'h00000001,
  parameter bit [31:0] SHIM_VERSION_1 = 32'h00000000,

  parameter bit [11:0] SHIM_REGISTER_ADDRESS_OFFSET = 12'h100,

  parameter int        ADDR_WIDTH = top_pkg::TL_AW,
  parameter int        DATA_WIDTH = top_pkg::TL_DW,
  parameter int        MASK_WIDTH = DATA_WIDTH >> 3,
  parameter int        USER_WIDTH = 32,
  parameter int        ID_WIDTH = top_pkg::TL_AIW,

  parameter bit        EnableDataIntgGen = 1,
  parameter bit        EnableRspDataIntgCheck = 1
) (
  input clk_i,
  input rst_ni,

  output tl_h2d_t tl_o,
  input  tl_d2h_t tl_i,

  // Shim interface
  input  logic                  dv_i,
  output logic                  hld_o,
  input  logic [ADDR_WIDTH-1:0] addr_i,
  input  logic                  write_i,
  input  logic [DATA_WIDTH-1:0] wdata_i,
  input  logic [MASK_WIDTH-1:0] wstrb_i,
  input  logic [2:0]            size_i,
  output logic [DATA_WIDTH-1:0] rdata_o,
  output logic                  error_o,
  // Optional signals
  input  logic                  last_i,
  input  logic [USER_WIDTH-1:0] user_i,
  input  logic [ID_WIDTH-1:0]   id_i
);

  // Differentiate between two levels of acknowledgements:
  //  - `req_ack`: A host-to-device request is acknowledged by the device,
  //     meaning that the response is pending.
  //  - `resp_ack`: The device-to-host response is acknowledged.
  logic pending_d, pending_q;
  logic req_ack, resp_ack;

  assign req_ack =  dv_i & tl_i.a_ready & tl_o.a_valid & ~internal_read;
  assign resp_ack = dv_i & tl_o.d_ready & tl_i.d_valid & ~internal_read;

  always_comb begin
    pending_d = pending_q;
    if (req_ack) begin
      pending_d = 1'b1;
    end else if (resp_ack) begin
      pending_d = 1'b0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pending_q <= 1'b0;
    end else begin
      pending_q <= pending_d;
    end
  end

  // Only make a new request (through `a_valid`) to the device when none are
  // pending. If the integrity checks are enabled, the `a_user` fields will be
  // set by the corresponding module (see `tlul_cmd_intg_gen`).
  tlul_pkg::tl_h2d_t tl_o_pre;
  assign tl_o_pre = '{
    a_valid: dv_i & ~pending_q & ~internal_read,
    a_opcode: ~write_i ? Get : (&wstrb_i ? PutFullData : PutPartialData),
    a_size: top_pkg::TL_SZW'(size_i),
    a_mask: wstrb_i,
    a_source: id_i,
    a_address: addr_i,
    a_data: wdata_i,
    a_user: '{default: '0, instr_type: prim_mubi_pkg::MuBi4False},
    d_ready: 1'b1,
    // unused
    a_param: 3'h0
  };

  logic internal_read;
  assign internal_read = |(addr_i[11:0] & SHIM_REGISTER_ADDRESS_OFFSET);

  // Accesses to shim internal registers have no latency. Accesses to device registers are
  // acknowledged with the TLUL d-channel handshake.
  assign hld_o = !pending_q && internal_read               ? 1'b0 :
                 pending_q && tl_o.d_ready && tl_i.d_valid ? 1'b0 : 1'b1;

  // A read request to an internal register is resolved in the same clock cycle.
  always_comb begin
    rdata_o = tl_i.d_data;
    if (internal_read) begin
      unique case (addr_i[3:0])
        4'h0:    rdata_o = SHIM_NAME_0;
        4'h4:    rdata_o = SHIM_NAME_1;
        4'h8:    rdata_o = SHIM_VERSION_0;
        4'hc:    rdata_o = SHIM_VERSION_1;
        default: rdata_o = tl_i.d_data;
      endcase
    end
  end

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

  assign error_o = tl_i.d_error | intg_err_chk;

  logic unused_signals;
  assign unused_signals = ^{last_i, user_i, size_i[2]};

  // Make sure the shim parameters are compatible with TLUL datapath widths.
  `ASSERT_INIT(TlInvalidAddrWidth_A, ADDR_WIDTH == top_pkg::TL_AW)
  `ASSERT_INIT(TlInvalidDataWidth_A, DATA_WIDTH == top_pkg::TL_DW)
  `ASSERT_INIT(TlInvalidMaskWidth_A, MASK_WIDTH == top_pkg::TL_DBW)
  `ASSERT_INIT(TlInvalidUserWidth_A, ID_WIDTH == top_pkg::TL_AIW)

endmodule
