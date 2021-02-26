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
    PutFullData    = 3'h 0,
    PutPartialData = 3'h 1,
    Get            = 3'h 4
  } tl_a_op_e;

  typedef enum logic [2:0] {
    AccessAck     = 3'h 0,
    AccessAckData = 3'h 1
  } tl_d_op_e;

  typedef enum logic [2:0] {
    InstrEn       = 3'b101,
    InstrDis      = 3'b010
  } tl_instr_en_e;

  // used for intermodule connections
  typedef tl_instr_en_e tl_instr_en_t;

  typedef enum logic [1:0] {
    InstrType     = 2'b01,
    DataType      = 2'b10
  } tl_type_e;

  // Even though it is codified this way, all values
  // NOT CheckDis is considered CheckEn
  typedef enum logic [1:0] {
    CheckDis      = 2'b01,
    CheckEn       = 2'b10
  } tl_chk_en_e;

  parameter int H2DCmdMaxWidth = 57;
  parameter int H2DCmdChkWidth = 7;
  parameter int D2HRspMaxWidth = 57;
  parameter int D2HRspChkWidth = 7;

  //parameter int H2DPayLoadFullWidth = H2DPayLoadMaxWidth + H2DPayLoadChkWidth;
  parameter int DataMaxWidth = 32;
  parameter int DataChkWidth = 7;

  typedef struct packed {
    logic [2:0]                    rsvd1;    // Reserved for future use
    tl_type_e                      tl_type;
    tl_chk_en_e                    chk_en;
    logic [H2DCmdChkWidth-1:0]     chk_cmd;
    logic [DataChkWidth-1:0]       chk_data;
  } tl_a_user_t;

  parameter tl_a_user_t TL_A_USER_DEFAULT = '{
    rsvd1: '0,
    tl_type: DataType,
    // This value is temporary
    chk_en: CheckDis,
    chk_cmd:  '0,
    chk_data: '0
  };

  typedef struct packed {
    logic   [top_pkg::TL_AW-1:0]  addr;
    tl_a_op_e                     opcode;
    logic  [top_pkg::TL_DBW-1:0]  mask;
  } tl_h2d_cmd_chk_t;

  typedef struct packed {
    logic                         a_valid;
    tl_a_op_e                     a_opcode;
    logic                  [2:0]  a_param;
    logic  [top_pkg::TL_SZW-1:0]  a_size;
    logic  [top_pkg::TL_AIW-1:0]  a_source;
    logic   [top_pkg::TL_AW-1:0]  a_address;
    logic  [top_pkg::TL_DBW-1:0]  a_mask;
    logic   [top_pkg::TL_DW-1:0]  a_data;
    tl_a_user_t                   a_user;

    logic                         d_ready;
  } tl_h2d_t;

  localparam tl_h2d_t TL_H2D_DEFAULT = '{
    d_ready:  1'b1,
    a_opcode: tl_a_op_e'('0),
    a_user:   tl_a_user_t'('0),
    default:  '0
  };

  typedef struct packed {
    logic [4:0]                    rsvd1;    // Reserved for future use
    tl_chk_en_e                    chk_en;
    logic [D2HRspChkWidth-1:0]     chk_rsp;
  } tl_d_user_t;

  parameter tl_d_user_t TL_D_USER_DEFAULT = '{
    rsvd1: '0,
    chk_en: CheckDis,
    chk_rsp: '0
  };

  typedef struct packed {
    logic                         d_valid;
    tl_d_op_e                     d_opcode;
    logic                  [2:0]  d_param;
    logic  [top_pkg::TL_SZW-1:0]  d_size;   // Bouncing back a_size
    logic  [top_pkg::TL_AIW-1:0]  d_source;
    logic  [top_pkg::TL_DIW-1:0]  d_sink;
    logic   [top_pkg::TL_DW-1:0]  d_data;
    tl_d_user_t                   d_user;
    logic                         d_error;

    logic                         a_ready;

  } tl_d2h_t;

  typedef struct packed {
    tl_d_op_e                     opcode;
    logic  [top_pkg::TL_SZW-1:0]  size;
    logic  [top_pkg::TL_AIW-1:0]  source;
    logic                         error;
  } tl_d2h_rsp_chk_t;

  localparam tl_d2h_t TL_D2H_DEFAULT = '{
    a_ready:  1'b1,
    d_opcode: tl_d_op_e'('0),
    d_user:   tl_d_user_t'(0),
    default:  '0
  };

  // Check user for unsupported values
  function automatic logic tl_a_user_chk(tl_a_user_t user);
    logic malformed_err;
    logic unused_user;
    unused_user = |user;
    malformed_err = ~(user.tl_type inside {InstrType, DataType}) |
                    ~(user.chk_en inside {CheckDis, CheckEn});
    return malformed_err;
  endfunction // tl_a_user_chk

  // extract variables used for command checking
  function automatic tl_h2d_cmd_chk_t extract_h2d_cmd_chk(tl_h2d_t tl);
    tl_h2d_cmd_chk_t payload;
    logic unused_tlul;
    unused_tlul = ^tl;
    payload.addr = tl.a_address;
    payload.opcode = tl.a_opcode;
    payload.mask = tl.a_mask;
    return payload;
  endfunction // extract_h2d_payload

  // extract variables used for response checking
  function automatic tl_d2h_rsp_chk_t extract_d2h_rsp_chk(tl_d2h_t tl);
    tl_d2h_rsp_chk_t payload;
    logic unused_tlul;
    unused_tlul = ^tl;
    payload.opcode = tl.d_opcode;
    payload.size   = tl.d_size;
    payload.source = tl.d_source;
    payload.error  = tl.d_error;
    return payload;
  endfunction // extract_d2h_rsp_chk

endpackage
