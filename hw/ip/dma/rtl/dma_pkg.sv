// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package dma_pkg;

  // Possible error bits the DMA can raise
  typedef enum logic [3:0] {
    DmaSourceAddrErr,
    DmaDestinationAddrErr,
    DmaOpcodeErr,
    DmaSizeErr,
    DmaCompletionErr,
    DmaBaseLimitErr,
    DmaGoConfigErr,
    DmaAsidErr,
    DmaErrLast
  } dma_error_e;


  // ASID uses a 4-bit FI protected encoding with a minimum Hamming distance of 2-bit
  typedef enum logic [3:0] {
    OtInternalAddr = 4'h7,
    SocControlAddr = 4'ha,
    SocSystemAddr  = 4'h9,
    OtExtFlashAddr = 4'hc
  } asid_encoding_e;

  // Supported opcodes by the DMA
  typedef enum logic [3:0] {
    OpcCopy   = 4'h0,
    OpcSha256 = 4'h1,
    OpcSha384 = 4'h2,
    OpcSha512 = 4'h3
  } opcode_e;

  typedef enum logic [4:0] {
    DmaIdle                  = 5'b00000,
    DmaClearPlic             = 5'b00001,
    DmaWaitClearPlicResponse = 5'b00010,
    DmaAddrSetup             = 5'b00011,
    DmaSendHostRead          = 5'b00100,
    DmaWaitHostReadResponse  = 5'b00101,
    DmaSendCtnRead           = 5'b00110,
    DmaWaitCtnReadResponse   = 5'b00111,
    DmaSendSysRead           = 5'b01000,
    DmaWaitSysReadResponse   = 5'b01001,
    DmaSendHostWrite         = 5'b01010,
    DmaWaitHostWriteResponse = 5'b01011,
    DmaSendCtnWrite          = 5'b01100,
    DmaWaitCtnWriteResponse  = 5'b01101,
    DmaSendSysWrite          = 5'b01110,
    DmaError                 = 5'b01111,
    DmaShaFinalize           = 5'b10000,
    DmaShaWait               = 5'b10001
  } dma_ctrl_state_e;

  ////////////////////////////
  // System Port Interfaces //
  ////////////////////////////

  parameter int unsigned SYS_NUM_REQ_CH      = 2;
  parameter int unsigned SYS_ADDR_WIDTH      = 64;
  parameter int unsigned SYS_METADATA_WIDTH  = 7;
  parameter int unsigned SYS_RACL_WIDTH      = 4;
  parameter int unsigned SYS_DATA_BYTEWIDTH  = 4;
  parameter int unsigned SYS_DATA_WIDTH      = SYS_DATA_BYTEWIDTH * 8;
  parameter int unsigned SYS_NUM_ERROR_TYPES = 1;
  parameter int unsigned NUM_LSIO_TRIGGERS   = 4;

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

  // Request command type
  typedef enum logic {
    SysCmdRead  = 1'd0,
    SysCmdWrite = 1'd1
  } sys_cmd_type_e;

  // System port request interface
  typedef struct packed {
    logic     [SYS_NUM_REQ_CH-1:0]                         vld_vec;
    logic     [SYS_NUM_REQ_CH-1:0][SYS_METADATA_WIDTH-1:0] metadata_vec;
    sys_opc_e [SYS_NUM_REQ_CH-1:0]                         opcode_vec;
    logic     [SYS_NUM_REQ_CH-1:0][SYS_ADDR_WIDTH-1:0]     iova_vec;
    logic     [SYS_NUM_REQ_CH-1:0][SYS_RACL_WIDTH-1:0]     racl_vec;
    logic     [SYS_DATA_WIDTH-1:0]                         write_data;
    logic     [SYS_DATA_BYTEWIDTH-1:0]                     write_be;
    logic     [SYS_DATA_BYTEWIDTH-1:0]                     read_be;
  } sys_req_t;

  // System port response interface
  typedef struct packed {
    logic [SYS_NUM_REQ_CH-1:0]         grant_vec;
    logic                              read_data_vld;
    logic [(SYS_DATA_BYTEWIDTH*8)-1:0] read_data;
    logic [SYS_METADATA_WIDTH-1:0]     read_metadata;
    logic                              error_vld;
    logic [SYS_NUM_ERROR_TYPES-1:0]    error_vec;
  } sys_rsp_t;

endpackage
