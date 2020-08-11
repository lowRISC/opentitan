// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package tlul_pkg;

  // this can be either PPC or BINTREE
  // there is no functional difference, but timing and area behavior is different
  // between the two instances. PPC can result in smaller implementations when timing
  // is not critical, whereas BINTREE is favorable when timing pressure is high (but this
  // may also result in a larger implementation). on FPGA targets, BINTREE is favorable
  // both in terms of area and timing.
  parameter ArbiterImpl = "PPC";

  typedef enum logic [2:0] {
    PutFullData = 3'h0,
    PutPartialData = 3'h1,
    Get = 3'h4
  } tl_a_op_e;
  typedef enum logic [2:0] {
    AccessAck = 3'h0,
    AccessAckData = 3'h1
  } tl_d_op_e;

  typedef struct packed {
    logic [6:0] rsvd1;  // Reserved for future use
    logic parity_en;
    logic [7:0] parity;  // Use only lower TL_DBW bit
  } tl_a_user_t;

  typedef struct packed {
    logic a_valid;
    tl_a_op_e a_opcode;
    logic [2:0] a_param;
    logic [top_pkg::TL_SZW-1:0] a_size;
    logic [top_pkg::TL_AIW-1:0] a_source;
    logic [top_pkg::TL_AW-1:0] a_address;
    logic [top_pkg::TL_DBW-1:0] a_mask;
    logic [top_pkg::TL_DW-1:0] a_data;
    tl_a_user_t a_user;

    logic d_ready;
  } tl_h2d_t;

  localparam tl_h2d_t TL_H2D_DEFAULT = '{d_ready: 1'b1, default: '0};

  typedef struct packed {
    logic d_valid;
    tl_d_op_e d_opcode;
    logic [2:0] d_param;
    logic [top_pkg::TL_SZW-1:0] d_size;  // Bouncing back a_size
    logic [top_pkg::TL_AIW-1:0] d_source;
    logic [top_pkg::TL_DIW-1:0] d_sink;
    logic [top_pkg::TL_DW-1:0] d_data;
    logic [top_pkg::TL_DUW-1:0] d_user;
    logic d_error;

    logic a_ready;
  } tl_d2h_t;

  localparam tl_d2h_t TL_D2H_DEFAULT = '{a_ready: 1'b1, default: '0};
endpackage
