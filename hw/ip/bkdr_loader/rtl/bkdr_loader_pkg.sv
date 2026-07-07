// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "bkdr_loader.svh"

package bkdr_loader_pkg;

  import bkdr_loader_reg_pkg::*;

  localparam int unsigned AddrWidth            = 32'd32;
  localparam int unsigned RegWidth             = 32'd32;
  localparam int unsigned MaxWordWidthIdxWidth = $clog2(MaxWordWidthDiv32);

  typedef struct packed {
    bit [ 3:0]  version;
    bit [15:0]  part_num;
    bit [10:0]  manufacturer;
    bit         _one;
  } bkdr_jtag_idcode_t;

  localparam bkdr_jtag_idcode_t BkdrIdCode = '{
    _one:          1'b1,                /* must be 1 */
    manufacturer: {4'd12, 7'b110_1111}, /* lowRISC */
    part_num:     16'h3000,             /* TAP_ID 3, PART_NUM 0 */
    version:       4'h0                 /* 1st Version */
  };

  typedef logic [AddrWidth-1:0]               addr_t;
  typedef logic [RegWidth-1:0]                reg_t;
  typedef logic [MaxWordWidthDiv32-1:0][31:0] word_t;
  typedef logic [TargetIdxWidth-1:0]          tgt_idx_t;

  // Target indices
  typedef enum logic [TargetIdxWidth-1:0] {
    BkdrAon       = 'd12,
    BkdrFlashB1I2 = 'd11,
    BkdrFlashB1I1 = 'd10,
    BkdrFlashB1I0 = 'd9,
    BkdrFlashB1   = 'd8,
    BkdrFlashB0I2 = 'd7,
    BkdrFlashB0I1 = 'd6,
    BkdrFlashB0I0 = 'd5,
    BkdrFlashB0   = 'd4,
    BkdrSramSec   = 'd3,
    BkdrSram      = 'd2,
    BkdrRom       = 'd1,
    BkdrOtp       = 'd0
  } bkdr_idx_e;

  // Valid targets
  localparam bkdr_idx_e BkdrValidTgts [NumBkdrTgts] = {
    BkdrAon,
    BkdrFlashB1I2,
    BkdrFlashB1I1,
    BkdrFlashB1I0,
    BkdrFlashB1,
    BkdrFlashB0I2,
    BkdrFlashB0I1,
    BkdrFlashB0I0,
    BkdrFlashB0,
    BkdrSramSec,
    BkdrSram,
    BkdrRom,
    BkdrOtp
  };

  // Strings describing the targets (max, 4 chars)
  localparam reg_t [NumBkdrTgts-1:0] BkdrTargets = {
    "AON ",
    "FI12",
    "FI11",
    "FI10",
    "FB1 ",
    "FI02",
    "FI01",
    "FI00",
    "FB0 ",
    "SRM2",
    "SRAM",
    "ROM ",
    "OTP "
  };

  typedef struct packed {
    logic  clk;
    logic  active;
    logic  write;
    addr_t addr;
    word_t wdata;
  } bkdr_req_t;

  typedef struct packed {
    word_t rdata;
    reg_t  param_width;
    reg_t  param_depth;
  } bkdr_rsp_t;

endpackage
