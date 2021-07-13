// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Asynchronous implementation of prim_subreg

module prim_subreg_async
  import prim_subreg_pkg::*;
#(
  parameter int            DW       = 32  ,
  parameter sw_access_e    SwAccess = SwAccessRW,
  parameter logic [DW-1:0] RESVAL   = '0    // Reset value
) (
  input clk_src_i,
  input rst_src_ni,
  input clk_dst_i,
  input rst_dst_ni,

  // destination sample pulse
  input src_update_i,

  // From SW: valid for RW, WO, W1C, W1S, W0C, RC
  // In case of RC, Top connects Read Pulse to we
  input          src_we_i,
  input [DW-1:0] src_wd_i,

  // From HW: valid for HRW, HWO
  input          dst_de_i,
  input [DW-1:0] dst_d_i,

  // output to Reg Read
  output logic          src_busy_o,
  output logic [DW-1:0] src_qs_o,

  // output to HW read
  output logic          dst_qe_o,
  // This output does not follow comportable convention to work with
  // current DV assumptions.
  output logic [DW-1:0] q
);

  logic dst_we;
  logic [DW-1:0] dst_wdata;
  logic [DW-1:0] q_int;

  prim_subreg_cdc #(
    .DW(DW),
    .RESVAL(RESVAL)
  ) u_reg_cdc (
    .clk_src_i,
    .rst_src_ni,
    .clk_dst_i,
    .rst_dst_ni,
    .src_update_i,
    .src_req_i(src_we_i),
    // data that crosses domain
    .src_data_i(src_wd_i),
    // data readback to software
    .src_data_o(src_qs_o),
    .src_busy_o,
    .dst_req_o(dst_we),
    // hardware written data
    .dst_data_i(q_int),
    // data to write to hardware
    .dst_data_o(dst_wdata)
  );

  prim_subreg #(
    .DW(DW),
    .SwAccess(SwAccess),
    .RESVAL(RESVAL)
  ) u_subreg (
    .clk_i(clk_dst_i),
    .rst_ni(rst_dst_ni),
    .we(dst_we),
    .wd(dst_wdata),
    .de(dst_de_i),
    .d(dst_d_i),
    .qe(dst_qe_o),
    .q(q_int),
    .qs()
  );
  assign q = q_int;

endmodule
