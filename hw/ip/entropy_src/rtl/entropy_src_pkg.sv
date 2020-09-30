// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//


package entropy_src_pkg;

  //-------------------------
  // Entropy Interface
  //-------------------------

  typedef struct packed {
    logic         es_ack;
    logic [383:0] es_bits;
    logic         es_fips;
  } entropy_src_hw_if_rsp_t;

  typedef struct packed {
    logic es_req;
  } entropy_src_hw_if_req_t;

  typedef struct packed {
    logic rng_enable;
  } entropy_src_rng_req_t;

  typedef struct packed {
    logic rng_ok;
    logic [3:0] rng_b;
  } entropy_src_rng_rsp_t;


endpackage : entropy_src_pkg
