// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// TL-UL socket 1:N module
//
// configuration settings
//   device_count: 4
//
// Verilog parameters
//   HReqPass:      if 1 then host requests can pass through on empty fifo,
//                  default 1
//   HRspPass:      if 1 then host responses can pass through on empty fifo,
//                  default 1
//   DReqPass:      (one per device_count) if 1 then device i requests can
//                  pass through on empty fifo, default 1
//   DRspPass:      (one per device_count) if 1 then device i responses can
//                  pass through on empty fifo, default 1
//   HReqDepth:     Depth of host request FIFO, default 2
//   HRspDepth:     Depth of host response FIFO, default 2
//   DReqDepth:     (one per device_count) Depth of device i request FIFO,
//                  default 2
//   DRspDepth:     (one per device_count) Depth of device i response FIFO,
//                  default 2
//
// Requests must stall to one device until all responses from other devices
// have returned.  Need to keep a counter of all outstanding requests and
// wait until that counter is zero before switching devices.
//
// This module will return a request error if the input value of 'dev_select_i'
// is not within the range 0..N-1. Thus the instantiator of the socket
// can indicate error by any illegal value of dev_select_i. 4'b1111 is
// recommended for visibility
//
// The maximum value of N is 15

`include "prim_assert.sv"

module tlul_socket_1n #(
  parameter int unsigned  N         = 4,
  parameter bit           HReqPass  = 1'b1,
  parameter bit           HRspPass  = 1'b1,
  parameter bit [N-1:0]   DReqPass  = {N{1'b1}},
  parameter bit [N-1:0]   DRspPass  = {N{1'b1}},
  parameter bit [3:0]     HReqDepth = 4'h2,
  parameter bit [3:0]     HRspDepth = 4'h2,
  parameter bit [N*4-1:0] DReqDepth = {N{4'h2}},
  parameter bit [N*4-1:0] DRspDepth = {N{4'h2}},
  localparam int unsigned NWD       = $clog2(N+1) // derived parameter
) (
  input                     clk_i,
  input                     rst_ni,
  input  tlul_pkg::tl_h2d_t tl_h_i,
  output tlul_pkg::tl_d2h_t tl_h_o,
  output tlul_pkg::tl_h2d_t tl_d_o    [N],
  input  tlul_pkg::tl_d2h_t tl_d_i    [N],
  input  [NWD-1:0]          dev_select_i
);

  `ASSERT_INIT(maxN, N < 32)

  // Since our steering is done after potential FIFOing, we need to
  // shove our device select bits into spare bits of reqfifo

  // instantiate the host fifo, create intermediate bus 't'

  // FIFO'd version of device select
  logic [NWD-1:0] dev_select_t;

  tlul_pkg::tl_h2d_t   tl_t_o;
  tlul_pkg::tl_d2h_t   tl_t_i;

  tlul_fifo_sync #(
    .ReqPass(HReqPass),
    .RspPass(HRspPass),
    .ReqDepth(HReqDepth),
    .RspDepth(HRspDepth),
    .SpareReqW(NWD)
  ) fifo_h (
    .clk_i,
    .rst_ni,
    .tl_h_i,
    .tl_h_o,
    .tl_d_o     (tl_t_o),
    .tl_d_i     (tl_t_i),
    .spare_req_i (dev_select_i),
    .spare_req_o (dev_select_t),
    .spare_rsp_i (1'b0),
    .spare_rsp_o ());


  // We need to keep track of how many requests are outstanding,
  // and to which device. New requests are compared to this and
  // stall until that number is zero.
  localparam int MaxOutstanding = 2**top_pkg::TL_AIW; // Up to 256 ounstanding
  localparam int OutstandingW = $clog2(MaxOutstanding+1);
  logic [OutstandingW-1:0] num_req_outstanding;
  logic [NWD-1:0]          dev_select_outstanding;
  logic                    hold_all_requests;
  logic                    accept_t_req, accept_t_rsp;

  assign  accept_t_req = tl_t_o.a_valid & tl_t_i.a_ready;
  assign  accept_t_rsp = tl_t_i.d_valid & tl_t_o.d_ready;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      num_req_outstanding <= '0;
      dev_select_outstanding <= '0;
    end else if (accept_t_req) begin
      if (!accept_t_rsp) begin
        `ASSERT_I(NotOverflowed_A, num_req_outstanding <= MaxOutstanding)
        num_req_outstanding <= num_req_outstanding + 1'b1;
      end
      dev_select_outstanding <= dev_select_t;
    end else if (accept_t_rsp) begin
      num_req_outstanding <= num_req_outstanding - 1'b1;
    end
  end

  assign hold_all_requests =
      (num_req_outstanding != '0) &
      (dev_select_t != dev_select_outstanding);

  // Make N copies of 't' request side with modified reqvalid, call
  // them 'u[0]' .. 'u[n-1]'.

  tlul_pkg::tl_h2d_t   tl_u_o [N+1];
  tlul_pkg::tl_d2h_t   tl_u_i [N+1];

  for (genvar i = 0 ; i < N ; i++) begin : gen_u_o
    assign tl_u_o[i].a_valid   = tl_t_o.a_valid &
                                 (dev_select_t == NWD'(i)) &
                                 ~hold_all_requests;
    assign tl_u_o[i].a_opcode  = tl_t_o.a_opcode;
    assign tl_u_o[i].a_param   = tl_t_o.a_param;
    assign tl_u_o[i].a_size    = tl_t_o.a_size;
    assign tl_u_o[i].a_source  = tl_t_o.a_source;
    assign tl_u_o[i].a_address = tl_t_o.a_address;
    assign tl_u_o[i].a_mask    = tl_t_o.a_mask;
    assign tl_u_o[i].a_data    = tl_t_o.a_data;
    assign tl_u_o[i].a_user    = tl_t_o.a_user;
  end

  tlul_pkg::tl_d2h_t tl_t_p ;

  // for the returning reqready, only look at the device we're addressing
  logic hfifo_reqready;
  always_comb begin
    hfifo_reqready = tl_u_i[N].a_ready; // default to error
    for (int idx = 0 ; idx < N ; idx++) begin
      //if (dev_select_outstanding == NWD'(idx)) hfifo_reqready = tl_u_i[idx].a_ready;
      if (dev_select_t == NWD'(idx)) hfifo_reqready = tl_u_i[idx].a_ready;
    end
    if (hold_all_requests) hfifo_reqready = 1'b0;
  end
  // Adding a_valid as a qualifier. This prevents the a_ready from having unknown value
  // when the address is unknown and the Host TL-UL FIFO is bypass mode.
  assign tl_t_i.a_ready = tl_t_o.a_valid & hfifo_reqready;

  always_comb begin
    tl_t_p = tl_u_i[N];
    for (int idx = 0 ; idx < N ; idx++) begin
      if (dev_select_outstanding == NWD'(idx)) tl_t_p = tl_u_i[idx];
    end
  end
  assign tl_t_i.d_valid  = tl_t_p.d_valid ;
  assign tl_t_i.d_opcode = tl_t_p.d_opcode;
  assign tl_t_i.d_param  = tl_t_p.d_param ;
  assign tl_t_i.d_size   = tl_t_p.d_size  ;
  assign tl_t_i.d_source = tl_t_p.d_source;
  assign tl_t_i.d_sink   = tl_t_p.d_sink  ;
  assign tl_t_i.d_data   = tl_t_p.d_data  ;
  assign tl_t_i.d_user   = tl_t_p.d_user  ;
  assign tl_t_i.d_error  = tl_t_p.d_error ;


  // accept responses from devices when selected if upstream is accepting
  for (genvar i = 0 ; i < N+1 ; i++) begin : gen_u_o_d_ready
    assign tl_u_o[i].d_ready = tl_t_o.d_ready;
  end

  // finally instantiate all device FIFOs and the error responder
  for (genvar i = 0 ; i < N ; i++) begin : gen_dfifo
    tlul_fifo_sync #(
      .ReqPass(DReqPass[i]),
      .RspPass(DRspPass[i]),
      .ReqDepth(DReqDepth[i*4+:4]),
      .RspDepth(DRspDepth[i*4+:4])
    ) fifo_d (
      .clk_i,
      .rst_ni,
      .tl_h_i      (tl_u_o[i]),
      .tl_h_o      (tl_u_i[i]),
      .tl_d_o      (tl_d_o[i]),
      .tl_d_i      (tl_d_i[i]),
      .spare_req_i (1'b0),
      .spare_req_o (),
      .spare_rsp_i (1'b0),
      .spare_rsp_o ());
  end

  assign tl_u_o[N].a_valid     = tl_t_o.a_valid &
                                 (dev_select_t == NWD'(N)) &
                                 ~hold_all_requests;
  assign tl_u_o[N].a_opcode    = tl_t_o.a_opcode;
  assign tl_u_o[N].a_param     = tl_t_o.a_param;
  assign tl_u_o[N].a_size      = tl_t_o.a_size;
  assign tl_u_o[N].a_source    = tl_t_o.a_source;
  assign tl_u_o[N].a_address   = tl_t_o.a_address;
  assign tl_u_o[N].a_mask      = tl_t_o.a_mask;
  assign tl_u_o[N].a_data      = tl_t_o.a_data;
  assign tl_u_o[N].a_user      = tl_t_o.a_user;
  tlul_err_resp err_resp (
    .clk_i,
    .rst_ni,
    .tl_h_i     (tl_u_o[N]),
    .tl_h_o     (tl_u_i[N]));

endmodule
