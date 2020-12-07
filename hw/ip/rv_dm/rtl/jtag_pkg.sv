// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package jtag_pkg;

  typedef struct packed {
    logic tck;
    logic tms;
    logic trst_n;
    logic tdi;
  } jtag_req_t;

  parameter jtag_req_t JTAG_REQ_DEFAULT = '0;

  typedef struct packed {
    logic tdo;
    logic tdo_oe;
  } jtag_rsp_t;

  parameter jtag_rsp_t JTAG_RSP_DEFAULT = '0;

endpackage : jtag_pkg
