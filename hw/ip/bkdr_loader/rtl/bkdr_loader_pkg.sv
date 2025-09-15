// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "bkdr_loader.svh"

package bkdr_loader_pkg;

  import bkdr_loader_reg_pkg::*;

  localparam int unsigned MaxWordWidth = 32'd32 * MaxWordWidthDiv32;
  localparam int unsigned AddrWidth    = 32'd32;
  localparam int unsigned RegWidth     = 32'd32;

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

  typedef logic [AddrWidth-1:0]    addr_t;
  typedef logic [RegWidth-1:0]     reg_t;
  typedef logic [MaxWordWidth-1:0] word_t;

  // Target indices
  typedef enum logic [$clog2(NumBkdrTgts)-1:0] {
    BkdrAon       = 32'd11,
    BkdrFlashB1I2 = 32'd10,
    BkdrFlashB1I1 = 32'd9,
    BkdrFlashB1I0 = 32'd8,
    BkdrFlashB1   = 32'd7,
    BkdrFlashB0I2 = 32'd6,
    BkdrFlashB0I1 = 32'd5,
    BkdrFlashB0I0 = 32'd4,
    BkdrFlashB0   = 32'd3,
    BkdrSram      = 32'd2,
    BkdrRom       = 32'd1,
    BkdrOtp       = 32'd0
  } bkdr_idx_e;

  // Valid targets
  localparam bkdr_idx_e [NumBkdrTgts-1:0] BkdrValidTgts = {
    BkdrAon,
    BkdrFlashB1I2,
    BkdrFlashB1I1,
    BkdrFlashB1I0,
    BkdrFlashB1,
    BkdrFlashB0I2,
    BkdrFlashB0I1,
    BkdrFlashB0I0,
    BkdrFlashB0,
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
