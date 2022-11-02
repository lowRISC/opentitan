// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// TL-UL socket M:1 module
//
// Verilog parameters
//   M:             Number of host ports.
//   HReqPass:      M bit array to allow requests to pass through the host i
//                  FIFO with no clock delay if the request FIFO is empty. If
//                  1'b0, at least one clock cycle of latency is created.
//                  Default is 1'b1.
//   HRspPass:      Same as HReqPass but for host response FIFO.
//   HReqDepth:     Mx4 bit array. bit[i*4+:4] is depth of host i request FIFO.
//                  Depth of zero is allowed if ReqPass is true. A maximum value
//                  of 16 is allowed, default is 2.
//   HRspDepth:     Same as HReqDepth but for host response FIFO.
//   DReqPass:      Same as HReqPass but for device request FIFO.
//   DRspPass:      Same as HReqPass but for device response FIFO.
//   DReqDepth:     Same as HReqDepth but for device request FIFO.
//   DRspDepth:     Same as HReqDepth but for device response FIFO.

`include "prim_assert.sv"

module tlul_socket_m1 #(
  parameter int unsigned  M         = 4,
  parameter bit [M-1:0]   HReqPass  = {M{1'b1}},
  parameter bit [M-1:0]   HRspPass  = {M{1'b1}},
  parameter bit [M*4-1:0] HReqDepth = {M{4'h1}},
  parameter bit [M*4-1:0] HRspDepth = {M{4'h1}},
  parameter bit           DReqPass  = 1'b1,
  parameter bit           DRspPass  = 1'b1,
  parameter bit [3:0]     DReqDepth = 4'h1,
  parameter bit [3:0]     DRspDepth = 4'h1
) (
  input                     clk_i,
  input                     rst_ni,

  input  tlul_pkg::tl_h2d_t tl_h_i [M],
  output tlul_pkg::tl_d2h_t tl_h_o [M],

  output tlul_pkg::tl_h2d_t tl_d_o,
  input  tlul_pkg::tl_d2h_t tl_d_i
);

  `ASSERT_INIT(maxM, M < 16)


  // Signals
  //
  //  tl_h_i/o[0] |  tl_h_i/o[1] | ... |  tl_h_i/o[M-1]
  //      |              |                    |
  // u_hostfifo[0]  u_hostfifo[1]        u_hostfifo[M-1]
  //      |              |                    |
  //       hreq_fifo_o(i) / hrsp_fifo_i(i)
  //     ---------------------------------------
  //     |       request/grant/req_data        |
  //     |                                     |
  //     |           PRIM_ARBITER              |
  //     |                                     |
  //     |  arb_valid / arb_ready / arb_data   |
  //     ---------------------------------------
  //                     |
  //                dreq_fifo_i / drsp_fifo_o
  //                     |
  //                u_devicefifo
  //                     |
  //                  tl_d_o/i
  //
  // Required ID width to distinguish between host ports
  //  Used in response steering
  localparam int unsigned IDW   = top_pkg::TL_AIW;
  localparam int unsigned STIDW = $clog2(M);

  tlul_pkg::tl_h2d_t hreq_fifo_o [M];
  tlul_pkg::tl_d2h_t hrsp_fifo_i [M];

  logic [M-1:0] hrequest;
  logic [M-1:0] hgrant;

  tlul_pkg::tl_h2d_t dreq_fifo_i;
  tlul_pkg::tl_d2h_t drsp_fifo_o;

  logic arb_valid;
  logic arb_ready;
  tlul_pkg::tl_h2d_t arb_data;

  // Host Req/Rsp FIFO
  for (genvar i = 0 ; i < M ; i++) begin : gen_host_fifo
    tlul_pkg::tl_h2d_t hreq_fifo_i;

    // ID Shifting
    logic [STIDW-1:0] reqid_sub;
    logic [IDW-1:0] shifted_id;
    assign reqid_sub = i;   // can cause conversion error?
    assign shifted_id = {
      tl_h_i[i].a_source[0+:(IDW-STIDW)],
      reqid_sub
    };

  `ASSERT(idInRange, tl_h_i[i].a_valid |-> tl_h_i[i].a_source[IDW-1 -:STIDW] == '0)

    // assign not connected bits to nc_* signal to make lint happy
    logic [IDW-1 : IDW-STIDW] unused_tl_h_source;
    assign unused_tl_h_source = tl_h_i[i].a_source[IDW-1 -: STIDW];

    // Put shifted ID
    assign hreq_fifo_i = '{
      a_valid:    tl_h_i[i].a_valid,
      a_opcode:   tl_h_i[i].a_opcode,
      a_param:    tl_h_i[i].a_param,
      a_size:     tl_h_i[i].a_size,
      a_source:   shifted_id,
      a_address:  tl_h_i[i].a_address,
      a_mask:     tl_h_i[i].a_mask,
      a_data:     tl_h_i[i].a_data,
      a_user:     tl_h_i[i].a_user,
      d_ready:    tl_h_i[i].d_ready
    };

    tlul_fifo_sync #(
      .ReqPass    (HReqPass[i]),
      .RspPass    (HRspPass[i]),
      .ReqDepth   (HReqDepth[i*4+:4]),
      .RspDepth   (HRspDepth[i*4+:4]),
      .SpareReqW  (1)
    ) u_hostfifo (
      .clk_i,
      .rst_ni,
      .tl_h_i      (hreq_fifo_i),
      .tl_h_o      (tl_h_o[i]),
      .tl_d_o      (hreq_fifo_o[i]),
      .tl_d_i      (hrsp_fifo_i[i]),
      .spare_req_i (1'b0),
      .spare_req_o (),
      .spare_rsp_i (1'b0),
      .spare_rsp_o ()
    );
  end

  // Device Req/Rsp FIFO
  tlul_fifo_sync #(
    .ReqPass    (DReqPass),
    .RspPass    (DRspPass),
    .ReqDepth   (DReqDepth),
    .RspDepth   (DRspDepth),
    .SpareReqW  (1)
  ) u_devicefifo (
    .clk_i,
    .rst_ni,
    .tl_h_i      (dreq_fifo_i),
    .tl_h_o      (drsp_fifo_o),
    .tl_d_o      (tl_d_o),
    .tl_d_i      (tl_d_i),
    .spare_req_i (1'b0),
    .spare_req_o (),
    .spare_rsp_i (1'b0),
    .spare_rsp_o ()
  );

  // Request Arbiter
  for (genvar i = 0 ; i < M ; i++) begin : gen_arbreqgnt
    assign hrequest[i] = hreq_fifo_o[i].a_valid;
  end

  assign arb_ready = drsp_fifo_o.a_ready;

  if (tlul_pkg::ArbiterImpl == "PPC") begin : gen_arb_ppc
    prim_arbiter_ppc #(
      .N          (M),
      .DW         ($bits(tlul_pkg::tl_h2d_t))
    ) u_reqarb (
      .clk_i,
      .rst_ni,
      .req_chk_i ( 1'b0        ), // TL-UL allows dropping valid without ready. See #3354.
      .req_i     ( hrequest    ),
      .data_i    ( hreq_fifo_o ),
      .gnt_o     ( hgrant      ),
      .idx_o     (             ),
      .valid_o   ( arb_valid   ),
      .data_o    ( arb_data    ),
      .ready_i   ( arb_ready   )
    );
  end else if (tlul_pkg::ArbiterImpl == "BINTREE") begin : gen_tree_arb
    prim_arbiter_tree #(
      .N          (M),
      .DW         ($bits(tlul_pkg::tl_h2d_t))
    ) u_reqarb (
      .clk_i,
      .rst_ni,
      .req_chk_i ( 1'b0        ), // TL-UL allows dropping valid without ready. See #3354.
      .req_i     ( hrequest    ),
      .data_i    ( hreq_fifo_o ),
      .gnt_o     ( hgrant      ),
      .idx_o     (             ),
      .valid_o   ( arb_valid   ),
      .data_o    ( arb_data    ),
      .ready_i   ( arb_ready   )
    );
  end else begin : gen_unknown
    `ASSERT_INIT(UnknownArbImpl_A, 0)
  end

  logic [  M-1:0] hfifo_rspvalid;
  logic [  M-1:0] dfifo_rspready;
  logic [IDW-1:0] hfifo_rspid;
  logic dfifo_rspready_merged;

  // arb_data --> dreq_fifo_i
  //   dreq_fifo_i.hd_rspready <= dfifo_rspready

  assign dfifo_rspready_merged = |dfifo_rspready;
  assign dreq_fifo_i = '{
    a_valid:   arb_valid,
    a_opcode:  arb_data.a_opcode,
    a_param:   arb_data.a_param,
    a_size:    arb_data.a_size,
    a_source:  arb_data.a_source,
    a_address: arb_data.a_address,
    a_mask:    arb_data.a_mask,
    a_data:    arb_data.a_data,
    a_user:    arb_data.a_user,

    d_ready:   dfifo_rspready_merged
  };

  // Response ID steering
  // drsp_fifo_o --> hrsp_fifo_i[i]

  // Response ID shifting before put into host fifo
  assign hfifo_rspid = {
    {STIDW{1'b0}},
    drsp_fifo_o.d_source[IDW-1:STIDW]
  };
  for (genvar i = 0 ; i < M ; i++) begin : gen_idrouting
    assign hfifo_rspvalid[i] = drsp_fifo_o.d_valid &
                               (drsp_fifo_o.d_source[0+:STIDW] == i);
    assign dfifo_rspready[i] = hreq_fifo_o[i].d_ready                &
                               (drsp_fifo_o.d_source[0+:STIDW] == i) &
                              drsp_fifo_o.d_valid;

    assign hrsp_fifo_i[i] = '{
      d_valid:  hfifo_rspvalid[i],
      d_opcode: drsp_fifo_o.d_opcode,
      d_param:  drsp_fifo_o.d_param,
      d_size:   drsp_fifo_o.d_size,
      d_source: hfifo_rspid,
      d_sink:   drsp_fifo_o.d_sink,
      d_data:   drsp_fifo_o.d_data,
      d_user:   drsp_fifo_o.d_user,
      d_error:  drsp_fifo_o.d_error,
      a_ready:  hgrant[i]
    };
  end

  // this assertion fails when rspid[0+:STIDW] not in [0..M-1]
  `ASSERT(rspIdInRange, drsp_fifo_o.d_valid |->
      drsp_fifo_o.d_source[0+:STIDW] >= 0 && drsp_fifo_o.d_source[0+:STIDW] < M)

endmodule
