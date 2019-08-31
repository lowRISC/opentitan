// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Faux Flash Erase Control
//

module flash_erase_ctrl #(
  parameter int AddrW = 10,
  parameter int WordsPerPage = 256,
  parameter int PagesPerBank = 256,
  parameter int EraseBitWidth = 1
) (
  // Software Interface
  input                     op_start_i,
  input [EraseBitWidth-1:0] op_type_i,
  input [AddrW-1:0]         op_addr_i,
  output logic              op_done_o,
  output logic              op_err_o,

  // Flash Macro Interface
  output logic             flash_req_o,
  output logic [AddrW-1:0] flash_addr_o,
  output logic [EraseBitWidth-1:0] flash_op_o,
  input                    flash_done_i,
  input                    flash_error_i
);

  import flash_ctrl_pkg::*;

  localparam int WordsBitWidth = $clog2(WordsPerPage);
  localparam int PagesBitWidth = $clog2(PagesPerBank);

  // The *AddrMask below masks out the bits that are not required
  // e.g, assume we have an address 0x5_0004_345C
  // 0x5 represents bank address
  // 0x0004 represents page address
  // PageAddrMask would be 0xF_FFFF_0000
  // BankAddrMask would be 0xF_0000_0000
  //
  localparam logic[AddrW-1:0] PageAddrMask = ~(('h1 << WordsBitWidth) - 1'b1);
  localparam logic[AddrW-1:0] BankAddrMask = ~(('h1 << (PagesBitWidth + WordsBitWidth)) - 1'b1);

  // IO assignments
  assign op_done_o = flash_req_o & flash_done_i;
  assign op_err_o = flash_req_o & flash_error_i;

  // Flash Interface assignments
  assign flash_req_o = op_start_i;
  assign flash_op_o = op_type_i;
  assign flash_addr_o = (op_type_i == PageErase) ?
                        op_addr_i & PageAddrMask :
                        op_addr_i & BankAddrMask;

  // unused bus
  logic [WordsBitWidth-1:0] unused_addr_i;
  assign unused_addr_i = op_addr_i[WordsBitWidth-1:0];

endmodule // flash_erase_ctrl
