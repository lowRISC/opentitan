// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package prim_otp_cfg_pkg;

  typedef struct packed {
    logic test;
  } otp_cfg_t;

  typedef struct packed {
    logic done;
  } otp_cfg_rsp_t;

  parameter otp_cfg_rsp_t OTP_CFG_DEFAULT = '0;

endpackage // prim_otp_cfg_pkg
