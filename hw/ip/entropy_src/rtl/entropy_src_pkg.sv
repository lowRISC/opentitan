// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package entropy_src_pkg;

  //-------------------------
  // Entropy Interface
  //-------------------------

  parameter int  CSRNG_BUS_WIDTH = 384;
  parameter int  FIPS_BUS_WIDTH  = 1;
  parameter int  FIPS_CSRNG_BUS_WIDTH = FIPS_BUS_WIDTH + CSRNG_BUS_WIDTH;

  // For a data width of N, there are 2^N buckets in the bucket health test, each with its own
  // counter. To make this health test scale reasonably well with `RngBusWidth`, we limit the bucket
  // health test to 4 bit. If `RngBusWidth` is larger than 4, the bucket health test gets
  // instantiated multiple times, once per 4 bit.
  parameter int BucketHtDataMaxWidth = 4;

  function automatic integer bucket_ht_data_width(integer rng_bus_width);
    return rng_bus_width >= BucketHtDataMaxWidth ? BucketHtDataMaxWidth : rng_bus_width;
  endfunction

  function automatic integer num_bucket_ht_inst(integer rng_bus_width);
    return prim_util_pkg::ceil_div(rng_bus_width, bucket_ht_data_width(rng_bus_width));
  endfunction

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

  // external health test i/f
  typedef struct packed {
    logic rng_bit_en;
    logic clear;
    logic active;
    logic [15:0] thresh_hi;
    logic [15:0] thresh_lo;
    logic window_wrap_pulse;
    logic threshold_scope;
  } entropy_src_xht_meta_req_t;

  typedef struct packed {
    logic[15:0] test_cnt_hi;
    logic[15:0] test_cnt_lo;
    logic continuous_test;
    logic test_fail_hi_pulse;
    logic test_fail_lo_pulse;
  } entropy_src_xht_meta_rsp_t;

  parameter entropy_src_xht_meta_req_t ENTROPY_SRC_XHT_META_REQ_DEFAULT = '{default: '0};
  parameter entropy_src_xht_meta_rsp_t ENTROPY_SRC_XHT_META_RSP_DEFAULT =
      '{test_cnt_lo: 16'hffff, default: '0};

  parameter int HT_WATERMARK_NUM_WIDTH = 4;
  typedef enum logic [HT_WATERMARK_NUM_WIDTH-1:0] {
    REPCNT_HI  = 0,
    REPCNTS_HI = 1,
    ADAPTP_HI  = 2,
    ADAPTP_LO  = 3,
    BUCKET_HI  = 4,
    MARKOV_HI  = 5,
    MARKOV_LO  = 6,
    EXTHT_HI   = 7,
    EXTHT_LO   = 8
  } ht_watermark_num_e;

endpackage : entropy_src_pkg
