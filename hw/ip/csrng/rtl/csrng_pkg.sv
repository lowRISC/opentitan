// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package csrng_pkg;

  //-------------------------
  // Application Interfaces
  //-------------------------

  parameter int unsigned   GENBITS_BUS_WIDTH = 128;
  parameter int unsigned   CSRNG_CMD_WIDTH = 32;
  parameter int unsigned   FIPS_GENBITS_BUS_WIDTH = entropy_src_pkg::FIPS_BUS_WIDTH + GENBITS_BUS_WIDTH;

  // instantiation interface
  typedef struct packed {
    logic         csrng_req_valid;
    logic [CSRNG_CMD_WIDTH-1:0]  csrng_req_bus;
    logic         genbits_ready;
  } csrng_req_t;

  typedef struct packed {
    logic         csrng_req_ready;
    logic         csrng_rsp_ack;
    logic         csrng_rsp_sts;
    logic         genbits_valid;
    logic         genbits_fips;
    logic [GENBITS_BUS_WIDTH-1:0] genbits_bus;
  } csrng_rsp_t;

  parameter csrng_req_t CSRNG_REQ_DEFAULT = '{default: '0};
  parameter csrng_rsp_t CSRNG_RSP_DEFAULT = '{default: '0};

  typedef enum logic [2:0] {
    INV = 3'h0,
    INS = 3'h1,
    RES = 3'h2,
    GEN = 3'h3,
    UPD = 3'h4,
    UNI = 3'h5,
    GENB = 3'h6,
    GENU = 3'h7
  } acmd_e;

endpackage : csrng_pkg
