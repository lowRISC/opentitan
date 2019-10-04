// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module xbar(
  input clk,
  input rst_n,

  xbar_if.device xhif0,
  xbar_if.device xhif1,
  xbar_if.host   xdif0,
  xbar_if.host   xdif1,
  xbar_if.host   xdif2
);

  hdb_fifo_sync #(
    .ReqPass  (1'b1),
    .RspPass  (1'b1),
    .ReqDepth (2),
    .RspDepth (2)
  ) u_dut (
    .clk_i    (xhif0.clk),
    .rst_ni   (rst_n),
    .hdb_h_i  (xhif0.host.h2d),
    .hdb_h_o  (xhif0.host.d2h),
    .hdb_d_o  (xdif0.device.h2d),
    .hdb_d_i  (xdif0.device.d2h)
  );
  /*
  assign xdif0.req_valid = xhif0.req_valid;
  assign xdif0.req_addr  = xhif0.req_addr ;
  assign xdif0.req_wr    = xhif0.req_wr   ;
  assign xdif0.req_wdata = xhif0.req_wdata;
  assign xdif0.req_wstrb = xhif0.req_wstrb;
  assign xdif0.req_attr  = xhif0.req_attr ;
  assign xdif0.req_id    = xhif0.req_id   ;
  assign xhif0.req_ready = xdif0.req_ready;

  assign xhif0.rsp_valid = xdif0.rsp_valid;
  assign xhif0.rsp_rdata = xdif0.rsp_rdata;
  assign xhif0.rsp_attr  = xdif0.rsp_attr ;
  assign xhif0.rsp_id    = xdif0.rsp_id   ;
  assign xdif0.rsp_ready = xhif0.rsp_ready;
  */

  hdb_fifo_async #(
    .ReqDepth (2),
    .RspDepth (2)
  ) u_dut_async (
    .clk_h_i  (xhif1.clk),
    .rst_h_ni (rst_n),
    .clk_d_i  (xdif1.clk),
    .rst_d_ni (rst_n),

    .hdb_h_i  (xhif1.host.h2d),
    .hdb_h_o  (xhif1.host.d2h),
    .hdb_d_o  (xdif1.device.h2d),
    .hdb_d_i  (xdif1.device.d2h)
  );

endmodule
