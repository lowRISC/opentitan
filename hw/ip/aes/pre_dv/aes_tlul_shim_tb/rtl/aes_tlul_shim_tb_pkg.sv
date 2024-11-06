// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package aes_tlul_shim_tb_pkg;

  import tlul_pkg::*;

  parameter bit AES_MANUAL_OPERATION    = 0;
  parameter bit AES_SIDELOAD            = 0;
  parameter int AES_GCM_NUM_VALID_BYTES = 16;

  parameter int AES_CTRL_OPERATION_OFFSET        = 0;
  parameter int AES_CTRL_MODE_OFFSET             = 2;
  parameter int AES_CTRL_KEY_LEN_OFFSET          = 8;
  parameter int AES_CTRL_SIDELOAD_OFFSET         = 11;
  parameter int AES_CTRL_PRNG_RESEED_RATE_OFFSET = 12;
  parameter int AES_CTRL_MANUAL_OPERATION_OFFSET = 15;

  parameter int AES_CTRL_GCM_PHASE_OFFSET           = 0;
  parameter int AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET = 6;

  parameter int AES_STATUS_IDLE_OFFSET         = 0;
  parameter int AES_STATUS_STALL_OFFSET        = 1;
  parameter int AES_STATUS_OUTPUT_LOST_OFFSET  = 2;
  parameter int AES_STATUS_OUTPUT_VALID_OFFSET = 3;
  parameter int AES_STATUS_INPUT_READY_OFFSET  = 4;

  typedef struct packed {
    logic                       dv;
    logic [top_pkg::TL_AW-1:0]  addr;
    logic                       write;
    logic [top_pkg::TL_DW-1:0]  wdata;
    logic [top_pkg::TL_DBW-1:0] wstrb;
    logic [2:0]                 size;
    logic                       last;
    logic [31:0]                user;
    logic [top_pkg::TL_AIW-1:0] id;

    // Internal signal to verify status bits.
    logic [top_pkg::TL_DW-1:0]  mask;
  } shim_request_t;

  function automatic shim_request_t write_request (logic [7:0] addr,
                                                   logic [top_pkg::TL_DW-1:0] wdata);
    shim_request_t req = '{
      dv: 1'b1,
      addr: {24'b0, addr},
      write: 1'b1,
      wdata: wdata,
      wstrb: top_pkg::TL_DBW'(4'b1111),
      size: 3'b010,
      last: 1'b0,
      user: 32'(TL_A_USER_DEFAULT),
      id: '{default: '0},
      mask: '{default: '0}
    };
    return req;
  endfunction

  function automatic shim_request_t read_request (logic [7:0] addr,
                                                  logic [top_pkg::TL_DW-1:0] mask = '0,
                                                  bit calyptra = 1'b0);
    shim_request_t req = '{
      dv: 1'b1,
      addr: {23'b0, calyptra, addr},
      write: 1'b0,
      wdata: '{default: '0},
      wstrb: top_pkg::TL_DBW'(4'b1111),
      size: 3'b010,
      last: 1'b0,
      user: 32'(TL_A_USER_DEFAULT),
      id: '{default: '0},
      mask: mask
    };
    return req;
  endfunction

endpackage
