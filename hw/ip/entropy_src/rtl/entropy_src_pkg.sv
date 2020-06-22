// Copyright lowRISC contributors.
// Licensed under the Apache License; Version 2.0; see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//


package entropy_src_pkg;

  //-------------------------
  // Entropy Interface
  //-------------------------

  typedef struct packed {
    logic        entropy_src_vld;
    logic [31:0] entropy_src_bits;
  } entropy_src_hw_if_rsp_t;

  parameter entropy_src_hw_if_rsp_t ENTROPY_SRC_HW_IF_RSP_DEFAULT = '{
    default: '0
  };

  typedef struct packed {
    logic entropy_src_rdy;
  } entropy_src_hw_if_req_t;

  parameter entropy_src_hw_if_req_t ENTROPY_SRC_HW_IF_REQ_DEFAULT = '{
    default: '0
  };

  typedef struct packed {
    logic rng_enable;
  } entropy_src_rng_req_t;

  parameter entropy_src_rng_req_t ENTROPY_SRC_RNG_REQ_DEFAULT = '{
    default: '0
  };

  typedef struct packed {
    logic rng_ok;
    logic [3:0] rng_b;
  } entropy_src_rng_rsp_t;

  parameter entropy_src_rng_rsp_t ENTROPY_SRC_RNG_RSP_DEFAULT = '{
    default: '0
  };

endpackage : entropy_src_pkg

