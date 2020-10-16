// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//


package csrng_pkg;

  //-------------------------
  // Application Interfaces
  //-------------------------

  // instantiation interface
  typedef struct packed {
    logic         csrng_req_valid;
    logic [31:0]  csrng_req_bus;
    logic         genbits_ready;
  } csrng_req_t;

  // default value of csrng_req_t (for dangling ports)
  parameter csrng_req_t CSRNG_REQ_DEFAULT = '{
    csrng_req_valid: 1'b0,
    csrng_req_bus:   '0,
    genbits_ready:   1'b0
  };


  typedef struct packed {
    logic         csrng_req_ready;
    logic         csrng_rsp_ack;
    logic         csrng_rsp_sts;
    logic         genbits_valid;
    logic         genbits_fips;
    logic [127:0] genbits_bus;
  } csrng_rsp_t;

  // default value of csrng_rsp_t (for dangling ports)
  parameter csrng_rsp_t CSRNG_RSP_DEFAULT = '{
    csrng_req_ready: 1'b0,
    csrng_rsp_ack: 1'b0,
    csrng_rsp_sts: 1'b0,
    genbits_valid:   1'b0,
    genbits_fips:   1'b0,
    genbits_bus:     '0
  };


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
