// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otp_ctrl_sync_wrap
  import otp_ctrl_pkg::*;
#(
  // Native OTP word size. This determines the size_i granule.
  parameter  int Width       = 16,
  parameter  int Depth       = 1024,
  // VMEM file to initialize the memory with
  parameter      MemInitFile = ""
) (
  input                             clk_i,
  input                             rst_ni,
  // Test clock for initial programming. Only used during RAW unlock
  input                             clk_raw_i,
  // Test enable input, overrides the OTP clock mux to use clk_i.
  input                             test_en_i,
    // Lifecycle broadcast inputs
  input  lc_ctrl_pkg::lc_tx_t       lc_raw_clk_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_dft_en_i,
  // Macro-specific power sequencing signals to/from AST
  output logic [OtpPwrSeqWidth-1:0] pwr_seq_o,
  input        [OtpPwrSeqWidth-1:0] pwr_seq_h_i,
  // Test interface
  input  tlul_pkg::tl_h2d_t         test_tl_i,
  output tlul_pkg::tl_d2h_t         test_tl_o,
  // Ready valid handshake for read/write command
  input                             req_i,
  output logic                      ack_o,
  input [OtpSizeWidth-1:0]          size_i, // #(Native words)-1, e.g. size == 0 for 1 native word.
  input [OtpCmdWidth-1:0]           cmd_i,  // 00: read command, 01: write command, 11: init command
  input [OtpAddrWidth-1:0]          addr_i,
  input [OtpIfWidth-1:0]            wdata_i,
  // Response channel
  output logic                      valid_o,
  output logic [OtpIfWidth-1:0]     rdata_o,
  output logic [OtpErrWidth-1:0]    err_o
);

  // Life cycle qualification of TL-UL test interface.
  tlul_pkg::tl_h2d_t     tl_win_h2d_gated;
  tlul_pkg::tl_d2h_t     tl_win_d2h_gated;
  assign tl_win_h2d_gated = (lc_dft_en_i == lc_ctrl_pkg::On) ? test_tl_i        : '0;
  assign test_tl_o        = (lc_dft_en_i == lc_ctrl_pkg::On) ? tl_win_d2h_gated : '0;

  // This clock mux is only steered to clk_raw_i if we are in the RAW life cycle state and the LC
  // controller initiates a RAW unlock transition. Consequently, the TL-UL test port of the OTP
  // wrapper does not require special synchronization logic, since it will never be active during
  // RAW. The functional OTP wrapper interface however needs to be treated as asynchronous.
  logic clk_otp;
  otp_ctrl_clk_mux u_otp_ctrl_clk_mux (
    .clk_i,
    .rst_ni,
    .clk_raw_i,
    .lc_raw_clk_en_i,
    .test_en_i,
    .clk_o ( clk_otp )
  );

  // Req/ack synchronizer for command data.
  logic otp_in_req, otp_in_ack;
  prim_sync_reqack u_sync_input (
    .clk_src_i  ( clk_i      ),
    .rst_src_ni ( rst_ni     ),
    .clk_dst_i  ( clk_raw_i  ),
    .rst_dst_ni ( rst_ni     ),
    .src_req_i  ( req_i      ),
    .src_ack_o  ( ack_o      ),
    .dst_req_o  ( otp_in_req ),
    .dst_ack_i  ( otp_in_ack )
  );

  // Req/ack synchronizer for read data.
  logic otp_out_req, otp_out_ack;
  prim_sync_reqack u_sync_output (
    .clk_src_i  ( clk_i       ),
    .rst_src_ni ( rst_ni      ),
    .clk_dst_i  ( clk_raw_i   ),
    .rst_dst_ni ( rst_ni      ),
    .src_req_i  ( otp_out_req ),
    .src_ack_o  ( otp_out_ack ),
    .dst_req_o  ( valid_o     ),
    // We are always ready to accept
    // the return data unconditionally.
    .dst_ack_i  ( 1'b1        )
  );

  prim_otp #(
    .Width ( OtpWidth ),
    .Depth ( OtpDepth )
  ) u_otp (
    // This muxed clock is switched to an external clock
    // when performing RAW unlock via the LC controller.
    .clk_i       ( clk_otp          ),
    .rst_ni,
    // Power sequencing signals to/from AST
    .pwr_seq_o,
    .pwr_seq_h_i,
    // Test interface
    .test_tl_i   ( tl_win_h2d_gated ),
    .test_tl_o   ( tl_win_d2h_gated ),
    // Read / Write command interface
    .ack_o       ( otp_in_ack       ),
    .req_i       ( otp_in_req       ),
    .cmd_i,
    .size_i,
    .addr_i,
    .wdata_i,
    // Read data out
    .ack_i       ( otp_out_ack      ),
    .req_o       ( otp_out_req      ),
    .rdata_o,
    .err_o
  );

endmodule : otp_ctrl_sync_wrap
