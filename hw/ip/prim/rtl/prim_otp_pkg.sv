// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Common interface definitions for OTP primitives.

package prim_otp_pkg;

  parameter int CmdWidth = 2;
  parameter int ErrWidth = 3;

  typedef enum logic [CmdWidth-1:0] {
    Read  = 2'b00,
    Write = 2'b01,
    Init  = 2'b11
  } cmd_e;

  typedef enum logic [ErrWidth-1:0] {
    NoError              = 3'h0,
    MacroError           = 3'h1,
    MacroEccCorrError    = 3'h2,
    MacroEccUncorrError  = 3'h3,
    MacroWriteBlankError = 3'h4
  } err_e;

endpackage : prim_otp_pkg
