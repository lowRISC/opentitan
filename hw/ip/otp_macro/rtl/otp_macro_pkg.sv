// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package otp_macro_pkg;

  parameter int OtpPwrSeqWidth     = 2;
  parameter int OtpTestCtrlWidth   = 32;
  parameter int OtpTestStatusWidth = 32;
  parameter int OtpTestVectWidth   = 8;

  // AST Interface

  typedef logic [OtpPwrSeqWidth-1:0] pwr_seq_t;
  typedef struct packed {
    pwr_seq_t pwr_seq;
  } otp_ast_req_t;

  typedef struct packed {
    pwr_seq_t pwr_seq_h;
  } otp_ast_rsp_t;

  // DFT interface
  typedef logic [OtpTestCtrlWidth-1:0] otp_test_ctrl_t;
  typedef struct packed {
    otp_test_ctrl_t ctrl;
  } otp_test_req_t;

  typedef logic [OtpTestStatusWidth-1:0] otp_test_status_t;
  typedef struct packed {
    otp_test_status_t status;
  } otp_test_rsp_t;

  typedef logic [OtpTestVectWidth-1:0] otp_test_vect_t;

  parameter otp_test_req_t OTP_TEST_DEFAULT = '0;

  // Config interface
  typedef struct packed {
    logic test;
  } otp_cfg_t;

  typedef struct packed {
    logic done;
  } otp_cfg_rsp_t;

  parameter otp_cfg_t OTP_CFG_DEFAULT = '0;

endpackage : otp_macro_pkg
