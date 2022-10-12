// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package entropy_src_pkg;

  //-------------------------
  // Entropy Interface
  //-------------------------

  parameter int  RNG_BUS_WIDTH   = 4;
  parameter int  CSRNG_BUS_WIDTH = 384;
  parameter int  FIPS_BUS_WIDTH  = 1;
  parameter int  FIPS_CSRNG_BUS_WIDTH = FIPS_BUS_WIDTH + CSRNG_BUS_WIDTH;
  // TODO: Should this be re-used in the RTL?
  parameter int  OBSERVE_FIFO_DEPTH = 64;


  // es entropy i/f
  typedef struct packed {
    logic es_ack;
    logic [CSRNG_BUS_WIDTH-1:0] es_bits;
    logic [FIPS_BUS_WIDTH-1:0] es_fips;
  } entropy_src_hw_if_rsp_t;

  typedef struct packed {
    logic es_req;
  } entropy_src_hw_if_req_t;

  parameter entropy_src_hw_if_req_t ENTROPY_SRC_HW_IF_REQ_DEFAULT = '{default: '0};
  parameter entropy_src_hw_if_rsp_t ENTROPY_SRC_HW_IF_RSP_DEFAULT = '{default: '0};


  // csrng block encrypt request/ack i/f
  typedef struct packed {
    logic cs_aes_halt_req;
  } cs_aes_halt_req_t;

  typedef struct packed {
    logic cs_aes_halt_ack;
  } cs_aes_halt_rsp_t;

  parameter cs_aes_halt_req_t CS_AES_HALT_REQ_DEFAULT = '{default: '0};
  parameter cs_aes_halt_rsp_t CS_AES_HALT_RSP_DEFAULT = '{default: '0};

  // ast rng i/f
  typedef struct packed {
    logic rng_enable;
  } entropy_src_rng_req_t;

  typedef struct packed {
    logic rng_valid;
    logic [RNG_BUS_WIDTH-1:0] rng_b;
  } entropy_src_rng_rsp_t;

  parameter entropy_src_rng_req_t ENTROPY_SRC_RNG_REQ_DEFAULT = '{default: '0};
  parameter entropy_src_rng_rsp_t ENTROPY_SRC_RNG_RSP_DEFAULT = '{default: '0};

  // external health test i/f
  typedef struct packed {
    logic [RNG_BUS_WIDTH-1:0] entropy_bit;
    logic entropy_bit_valid;
    logic clear;
    logic active;
    logic [15:0] thresh_hi;
    logic [15:0] thresh_lo;
    logic [15:0] health_test_window;
    logic window_wrap_pulse;
    logic threshold_scope;
  } entropy_src_xht_req_t;

  typedef struct packed {
    logic[15:0] test_cnt_hi;
    logic[15:0] test_cnt_lo;
    logic continuous_test;
    logic test_fail_hi_pulse;
    logic test_fail_lo_pulse;
  } entropy_src_xht_rsp_t;

  parameter entropy_src_xht_req_t ENTROPY_SRC_XHT_REQ_DEFAULT = '{default: '0};
  parameter entropy_src_xht_rsp_t ENTROPY_SRC_XHT_RSP_DEFAULT =
      '{test_cnt_lo: 16'hffff, default: '0};

endpackage : entropy_src_pkg
