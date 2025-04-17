// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Common interface definitions for OTP macro.

package otp_ctrl_macro_pkg;

  //////////////////////////////////////
  // Typedefs for OTP Macro Interface //
  //////////////////////////////////////

  // OTP-macro specific

  // The bit-width of the macro words.
  parameter int OtpWidth         = 16;
  // The total number of words.
  parameter int OtpDepth         = 1024;
  // The macro can transfer up to 4 native words per request, which is encoded
  // in 2 bits.
  parameter int OtpSizeWidth     = 2;
  parameter int OtpPwrSeqWidth   = 2;

  parameter int OtpAddrWidth     = 10;
  parameter int OtpIfWidth       = 2**OtpSizeWidth*OtpWidth;
  // Number of Byte address bits to cut off in order to get the native OTP word address.
  parameter int OtpAddrShift     = 1;

  typedef logic [OtpSizeWidth-1:0] otp_macro_size_t;
  typedef logic [OtpAddrWidth-1:0] otp_macro_addr_t;
  typedef logic [OtpIfWidth-1:0] otp_macro_data_t;

  // Command codes

  // The command is sparsely encoded to make it more difficult to tamper with.
  parameter int OtpCmdWidth = 7;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 4 -m 5 -n 7   //     -s 696743973 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: |||||||||||||||||||| (100.00%)
  //  5: --
  //  6: --
  //  7: --
  //
  // Minimum Hamming distance: 4
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 5
  //
  typedef enum logic [OtpCmdWidth-1:0] {
    Read     = 7'b1000101,
    Write    = 7'b0110111,
    // Raw commands ignore integrity
    ReadRaw  = 7'b1111001,
    WriteRaw = 7'b1100010,
    Init     = 7'b0101100
  } cmd_e;
  parameter int OtpErrWidth      = 3;

  // Error codes
  typedef enum logic [OtpErrWidth-1:0] {
    NoError              = 3'h0,
    MacroError           = 3'h1,
    MacroEccCorrError    = 3'h2,
    MacroEccUncorrError  = 3'h3,
    MacroWriteBlankError = 3'h4
  } err_e;

  typedef struct packed {
    logic valid;
    cmd_e cmd;
    otp_macro_size_t size;
    otp_macro_addr_t addr;
    otp_macro_data_t wdata;
  } otp_ctrl_macro_req_t;

  typedef struct packed {
    logic ready;
    logic rvalid;
    otp_macro_data_t rdata;
    err_e err;
    logic fatal_lc_fsm_err;
    logic fatal_alert;
    logic recov_alert;
  } otp_ctrl_macro_rsp_t;

endpackage : otp_ctrl_macro_pkg
