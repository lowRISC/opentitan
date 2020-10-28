// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//


package entropy_src_pkg;

  //-------------------------
  // Entropy Interface
  //-------------------------

  parameter int  RNG_DATA_WIDTH = 4, CSRNG_DATA_WIDTH = 384;

  // es entropy i/f
  typedef struct packed {
    logic         es_ack;
    logic [CSRNG_DATA_WIDTH-1:0] es_bits;
    logic         es_fips;
  } entropy_src_hw_if_rsp_t;

  typedef struct packed {
    logic es_req;
  } entropy_src_hw_if_req_t;


  // ast rng i/f
  typedef struct packed {
    logic rng_enable;
  } entropy_src_rng_req_t;

  typedef struct packed {
    logic rng_valid;
    logic [RNG_DATA_WIDTH-1:0] rng_b;
  } entropy_src_rng_rsp_t;

  // external health test i/f
  typedef struct packed {
    logic [3:0] entropy_bit;
    logic entropy_bit_valid;
    logic clear;
    logic active;
    logic [15:0] thresh_hi;
    logic [15:0] thresh_lo;
    logic [15:0] window;
  } entropy_src_xht_req_t;

  typedef struct packed {
    logic[15:0] test_cnt;
    logic test_fail_hi_pulse;
    logic test_fail_lo_pulse;
  } entropy_src_xht_rsp_t;


endpackage : entropy_src_pkg
