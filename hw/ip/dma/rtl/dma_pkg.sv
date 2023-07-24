// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package dma_pkg;

  // ASID uses a 4-bit FI protected encoding with a minimum Hamming distance of 2-bit
  typedef enum logic [3:0] {
    OtAddr    = 4'h7,
    SocAddr   = 4'ha,
    SysAddr   = 4'h9,
    FlashAddr = 4'hc
  } asid_encoding_e;

  ////////////////////////////
  // System Port Interfaces //
  ////////////////////////////

  parameter int unsigned SYS_NUM_REQ_CH      = 2;
  parameter int unsigned SYS_ADDR_WIDTH      = 64;
  parameter int unsigned SYS_METADATA_WIDTH  = 7;
  parameter int unsigned SYS_RACL_WIDTH      = 4;
  parameter int unsigned SYS_DATA_BYTEWIDTH  = 4;
  parameter int unsigned SYS_NUM_ERROR_TYPES = 1;

  // Supported Opcodes on the bus
  typedef enum logic [2:0] {
    SysOpcRead            = 3'd0,
    SysOpcCmoClean        = 3'd1,
    SysOpcAtomicNoDataRsp = 3'd2,
    SysOpcAtomicDataRsp   = 3'd3,
    SysOpcWrite           = 3'd4,
    SysOpcWriteOrdered    = 3'd5,
    SysOpcMsgIntrReq      = 3'd6,
    SysOpcMsgP2P          = 3'd7
  } sys_opc_e;

  // System port request interface
  typedef struct packed {
    logic     [SYS_NUM_REQ_CH-1:0]                         vld_vec;
    logic     [SYS_NUM_REQ_CH-1:0][SYS_ADDR_WIDTH-1:0]     metadata_vec;
    sys_opc_e [SYS_NUM_REQ_CH-1:0]                         opcode_vec;
    logic     [SYS_NUM_REQ_CH-1:0][SYS_METADATA_WIDTH-1:0] iova_vec;
    logic     [SYS_NUM_REQ_CH-1:0][SYS_RACL_WIDTH-1:0]     racl_vec;
    logic     [(SYS_DATA_BYTEWIDTH*8)-1:0]                 write_data;
    logic     [SYS_DATA_BYTEWIDTH-1:0]                     write_be;
    logic     [SYS_DATA_BYTEWIDTH-1:0]                     read_be;
  } sys_req_t;

  // System port response interface
  typedef struct packed {
    logic [SYS_NUM_REQ_CH-1:0]         req_grant_vec_i;
    logic                              read_data_vld_i;
    logic [(SYS_DATA_BYTEWIDTH*8)-1:0] read_data_i;
    logic [SYS_METADATA_WIDTH-1:0]     read_metadata_i;
    logic                              error_vld_i;
    logic [SYS_NUM_ERROR_TYPES-1:0]    error_vec_i;
  } sys_rsp_t;

endpackage
