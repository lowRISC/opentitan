// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//


package edn_pkg;
  ///////////////////////////
  // Peripheral Interfaces //
  ///////////////////////////

  // EDN request interface
  typedef struct packed {
    logic                                 edn_req;
  } edn_req_t;
  typedef struct packed {
    logic                                 edn_ack;
    logic                                 edn_fips;
  } edn_rsp_t;

  parameter edn_req_t EDN_REQ_DEFAULT = '{default: '0};
  parameter edn_rsp_t EDN_RSP_DEFAULT = '{default: '0};

endpackage : edn_pkg
