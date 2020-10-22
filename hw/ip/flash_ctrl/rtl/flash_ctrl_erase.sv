// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Faux Flash Erase Control
//

module flash_ctrl_erase import flash_ctrl_pkg::*; (
  // Software Interface
  input                       op_start_i,
  input flash_erase_e         op_type_i,
  input [BusAddrW-1:0]        op_addr_i,
  output logic                op_done_o,
  output logic                op_err_o,

  // Flash Macro Interface
  output logic                flash_req_o,
  output logic [BusAddrW-1:0] flash_addr_o,
  output flash_erase_e        flash_op_o,
  input                       flash_done_i,
  input                       flash_error_i
);

  import flash_ctrl_pkg::*;

  localparam int WordsBitWidth = $clog2(BusWordsPerPage);
  localparam int PagesBitWidth = $clog2(PagesPerBank);

  // The *AddrMask below masks out the bits that are not required
  // e.g, assume we have an address 0x5_0004_345C
  // 0x5 represents bank address
  // 0x0004 represents page address
  // PageAddrMask would be 0xF_FFFF_0000
  // BankAddrMask would be 0xF_0000_0000
  //
  localparam logic[BusAddrW-1:0] PageAddrMask = ~(('h1 << WordsBitWidth) - 1'b1);
  localparam logic[BusAddrW-1:0] BankAddrMask = ~(('h1 << (PagesBitWidth + WordsBitWidth)) - 1'b1);

  // IO assignments
  assign op_done_o = flash_req_o & flash_done_i;
  assign op_err_o = flash_req_o & flash_error_i;

  // Flash Interface assignments
  assign flash_req_o = op_start_i;
  assign flash_op_o = op_type_i;
  assign flash_addr_o = (op_type_i == FlashErasePage) ?
                        op_addr_i & PageAddrMask :
                        op_addr_i & BankAddrMask;

  // unused bus
  logic [WordsBitWidth-1:0] unused_addr_i;
  assign unused_addr_i = op_addr_i[WordsBitWidth-1:0];

endmodule // flash_ctrl_erase
