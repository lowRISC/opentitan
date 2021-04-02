// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Command & Configuration Options structure for SPI HOST.
//

package spi_host_cmd_pkg;

  parameter int CSW = prim_util_pkg::vbits(spi_host_reg_pkg::NumCS);
  parameter int CmdSize = CSW + 45;

  // For decoding the direction register
  typedef enum logic [1:0] {
     Dummy  = 2'b00,
     RdOnly = 2'b01,
     WrOnly = 2'b10,
     Bidir  = 2'b11
   } reg_direction_t;

  // For decoding the direction register
  typedef enum logic [1:0] {
     Standard = 2'b00,
     Dual     = 2'b01,
     Quad     = 2'b10,
     RsvdSpd  = 2'b11
   } speed_t;

  typedef struct packed {
    logic [15:0] clkdiv;
    logic [3:0]  csnidle;
    logic [3:0]  csnlead;
    logic [3:0]  csntrail;
    logic        full_cyc;
    logic        cpha;
    logic        cpol;
  } configopts_t;

  typedef struct packed {
    logic [1:0] speed;
    logic       cmd_wr_en;
    logic       cmd_rd_en;
    logic [8:0] len;
    logic       csaat;
  } segment_t;

  typedef struct packed {
    logic [CSW-1:0] csid;
    segment_t segment;
    configopts_t configopts;
  } command_t;

endpackage
