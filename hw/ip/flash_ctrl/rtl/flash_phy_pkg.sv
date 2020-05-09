// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash phy module package
//

package flash_phy_pkg;
  parameter int NumBanks     = flash_ctrl_pkg::NumBanks;
  parameter int PagesPerBank = flash_ctrl_pkg::PagesPerBank;
  parameter int WordsPerPage = flash_ctrl_pkg::WordsPerPage;
  parameter int BytesPerWord = flash_ctrl_pkg::BytesPerWord;
  parameter int BankW        = flash_ctrl_pkg::BankW;
  parameter int PageW        = flash_ctrl_pkg::PageW;
  parameter int WordW        = flash_ctrl_pkg::WordW;
  parameter int BusWidth     = flash_ctrl_pkg::BusWidth;
  parameter int DataWidth    = flash_ctrl_pkg::DataWidth;
  parameter int NumBuf       = 4; // number of flash read buffers
  parameter int RspOrderDepth = 2; // this should be DataWidth / BusWidth
                                   // will switch to this after bus widening

  // This address width is from the perspective of the sw / flash controller
  // which may assume a different width relative to the flash primitive
  parameter int BankAddrW = flash_ctrl_pkg::BankAddrW;

  // This address width is from the perspective of the flash primitive,
  // which is an integer multiple of the bus width.  As a result, the number
  // of relevant address bits changes.

  // address bits remain must be 0
  parameter int AddrBitsRemain = DataWidth % BusWidth;

  // must be powers of 2 multiple
  parameter int WidthMultiple = DataWidth / BusWidth;

  // number of flash words per page vs bus words per page
  parameter int FlashWordsPerPage = WordsPerPage / WidthMultiple;
  parameter int FlashWordsW = $clog2(FlashWordsPerPage);

  // base index
  // This is the lsb position of the prim flash address when looking at the bus address
  parameter int LsbAddrBit = $clog2(WidthMultiple);
  parameter int WordSelW = WidthMultiple == 1 ? 1 : LsbAddrBit;

  // prim flash addr width
  parameter int PrimFlashAddrW = BankAddrW - LsbAddrBit;

  // Read buffer metadata
  typedef enum logic [1:0] {
    Invalid     = 2'h0,
    Wip         = 2'h1,
    Valid       = 2'h2,
    Undef       = 2'h3
  } rd_buf_attr_e;

  typedef struct packed {
    logic [DataWidth-1:0] data;
    logic [PrimFlashAddrW-1:0] addr; // all address bits preserved to pick return portion
    rd_buf_attr_e attr;
  } rd_buf_t;

  typedef struct packed {
    logic [NumBuf-1:0] buf_sel;
    logic [WordSelW-1:0] word_sel;
  } rsp_fifo_entry_t;

  parameter int RspOrderFifoWidth = $bits(rsp_fifo_entry_t);

  // Flash Operations Supported
  typedef enum logic [2:0] {
    PhyRead      = 3'h0,
    PhyProg      = 3'h1,
    PhyPgErase   = 3'h2,
    PhyBkErase   = 3'h3,
    PhyOps       = 3'h4
  } flash_phy_op_e;

  // Flash Operations Selected
  typedef enum logic [1:0] {
    None         = 2'h0,
    Host         = 2'h1,
    Ctrl         = 2'h2
  } flash_phy_op_sel_e;




endpackage // flash_phy_pkg
