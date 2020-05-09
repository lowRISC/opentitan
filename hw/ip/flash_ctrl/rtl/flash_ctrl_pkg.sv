// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Controller module.
//

package flash_ctrl_pkg;

  // parameters for flash macro properties
  localparam int NumBanks        = top_pkg::FLASH_BANKS;
  localparam int PagesPerBank    = top_pkg::FLASH_PAGES_PER_BANK;
  localparam int WordsPerPage    = top_pkg::FLASH_WORDS_PER_PAGE;  //Number of bus words per page
  localparam int BytesPerWord    = top_pkg::FLASH_BYTES_PER_WORD;
  localparam int BankW           = $clog2(NumBanks);
  localparam int PageW           = $clog2(PagesPerBank);
  localparam int WordW           = $clog2(WordsPerPage);
  localparam int AddrW           = BankW + PageW + WordW; // all flash range
  localparam int BankAddrW       = PageW + WordW;         // 1 bank of flash range
  localparam int DataWidth       = 64;
  localparam int FlashTotalPages = NumBanks * PagesPerBank;
  localparam int AllPagesW       = BankW + PageW;

  // bus interface
  localparam int BusWidth        = top_pkg::TL_DW;

  // flash controller protection regions
  localparam int MpRegions       = 8;

  // fifo parameters
  localparam int FifoDepth       = 16;
  localparam int FifoDepthW      = $clog2(FifoDepth+1);


  // Flash Operations Supported
  typedef enum logic [1:0] {
    FlashRead      = 2'h0,
    FlashProg      = 2'h1,
    FlashErase     = 2'h2
  } flash_op_e;

  // Flash Erase Operations Supported
  typedef enum logic  {
    PageErase     = 0,
    BankErase     = 1
  } flash_erase_op_e;

  // Flash tlul to fifo direction
  typedef enum logic  {
    WriteDir     = 1'b0,
    ReadDir      = 1'b1
  } flash_flfo_dir_e;

  // Flash controller to memory
  typedef struct packed {
    logic                req;
    logic                rd;
    logic                prog;
    logic                pg_erase;
    logic                bk_erase;
    logic [AddrW-1:0]    addr;
    logic [BusWidth-1:0] prog_data;
  } flash_req_t;

  // default value of flash_req_t (for dangling ports)
  parameter flash_req_t FLASH_REQ_DEFAULT = '{
    req:       1'b0,
    rd:        1'b0,
    prog:      1'b0,
    pg_erase:  1'b0,
    bk_erase:  1'b0,
    addr:      '0,
    prog_data: '0
  };

  // memory to flash controller
  typedef struct packed {
    logic                rd_done;
    logic                prog_done;
    logic                erase_done;
    logic [BusWidth-1:0] rd_data;
    logic                init_busy;
  } flash_rsp_t;

  // default value of flash_rsp_t (for dangling ports)
  parameter flash_rsp_t FLASH_RSP_DEFAULT = '{
    rd_done:    1'b0,
    prog_done:  1'b0,
    erase_done: 1'b0,
    rd_data:    '0,
    init_busy:  1'b0
  };

endpackage : flash_ctrl_pkg
