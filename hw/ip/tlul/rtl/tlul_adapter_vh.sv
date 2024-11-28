// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module tlul_adapter_vh
  import tlul_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter int ADDR_WIDTH = top_pkg::TL_AW,
  parameter int DATA_WIDTH = top_pkg::TL_DW,
  parameter int MASK_WIDTH = DATA_WIDTH >> 3,
  parameter int USER_WIDTH = 32,
  parameter int ID_WIDTH   = top_pkg::TL_AIW,

  parameter bit [ADDR_WIDTH-1:0] VH_REGISTER_ADDRESS_OFFSET = 32'h0000_0100,

  parameter bit EnableDataIntgGen = 1,
  parameter bit EnableRspDataIntgCheck = 1
) (
  input                         clk_i,
  input                         rst_ni,

  output                        tl_h2d_t tl_o,
  input                         tl_d2h_t tl_i,

  // Valid-Hold device interface (VH to TLUL).
  input logic                   dv_i,
  output logic                  hld_o,
  input logic [ADDR_WIDTH-1:0]  addr_i,
  input logic                   write_i,
  input logic [DATA_WIDTH-1:0]  wdata_i,
  input logic [MASK_WIDTH-1:0]  wstrb_i,
  input logic [2:0]             size_i,
  output logic [DATA_WIDTH-1:0] rdata_o,
  output logic                  error_o,
  input logic                   last_i,
  input logic [USER_WIDTH-1:0]  user_i,
  input logic [ID_WIDTH-1:0]    id_i,

  // Valid-Hold host interface (VH to internal registers). The signals from the VH device interface
  // are routed to the VH host interface for every internal access, see the `internal_access` signal.
  output logic                  int_dv_o,
  input logic                   int_hld_i,
  output logic [ADDR_WIDTH-1:0] int_addr_o,
  output logic                  int_write_o,
  output logic [DATA_WIDTH-1:0] int_wdata_o,
  output logic [MASK_WIDTH-1:0] int_wstrb_o,
  output logic [2:0]            int_size_o,
  input logic [DATA_WIDTH-1:0]  int_rdata_i,
  input logic                   int_error_i,
  output logic                  int_last_o,
  output logic [USER_WIDTH-1:0] int_user_o,
  output logic [ID_WIDTH-1:0]   int_id_o
);

  // Differentiate between two levels of acknowledgements:
  //  - `req_ack`: A host-to-device request is acknowledged by the device, meaning that the response
  //    is pending.
  //  - `resp_ack`: The device-to-host response is acknowledged.
  logic pending_d, pending_q;
  logic req_ack, resp_ack;

  assign req_ack =  dv_i & tl_i.a_ready & tl_o.a_valid & ~internal_access;
  assign resp_ack = dv_i & tl_o.d_ready & tl_i.d_valid & ~internal_access;

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

  // Only make a new request (through `a_valid`) to the device when none are pending. If the
  // integrity checks are enabled, the `a_user` fields will be set by the corresponding module (see
  // `tlul_cmd_intg_gen`).
  tlul_pkg::tl_h2d_t tl_o_pre;
  assign tl_o_pre = '{
    a_valid: dv_i & ~pending_q & ~internal_access,
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

  // The adapter distinguishes between two types of VH accesses: those going to an internal register
  // file and those targeting OpenTitan registers, with the latter ones being translated into TLUL
  // requests while the other requests are relayed to the internal register file.
  logic internal_access;
  assign internal_access = addr_i >= VH_REGISTER_ADDRESS_OFFSET;

  // Accesses to device registers are acknowledged with the TLUL d-channel handshake.
  assign hld_o = !pending_q && internal_access && !int_hld_i ? 1'b0 :
                  pending_q && tl_o.d_ready && tl_i.d_valid  ? 1'b0 : 1'b1;

  assign rdata_o = internal_access ? int_rdata_i : tl_i.d_data;

  // Route signals to the VH host interface.
  assign int_dv_o    = dv_i & internal_access;
  assign int_addr_o  = addr_i;
  assign int_write_o = write_i;
  assign int_wdata_o = wdata_i;
  assign int_wstrb_o = wstrb_i;
  assign int_size_o  = size_i;
  assign int_last_o  = last_i;
  assign int_user_o  = user_i;
  assign int_id_o    = id_i;

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

  assign error_o = tl_i.d_error | int_error_i | intg_err_chk;

  // Make sure the VH parameters are compatible with TLUL datapath widths.
  `ASSERT_INIT(TlInvalidAddrWidth_A, ADDR_WIDTH == top_pkg::TL_AW)
  `ASSERT_INIT(TlInvalidDataWidth_A, DATA_WIDTH == top_pkg::TL_DW)
  `ASSERT_INIT(TlInvalidMaskWidth_A, MASK_WIDTH == top_pkg::TL_DBW)
  `ASSERT_INIT(TlInvalidUserWidth_A, ID_WIDTH == top_pkg::TL_AIW)

endmodule
