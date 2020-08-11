// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Controller module.
//

package flash_ctrl_pkg;

  // design constants
  parameter int DataWidth = top_pkg::FLASH_DATA_WIDTH;
  parameter int NumBanks = top_pkg::FLASH_BANKS;
  parameter int InfosPerBank = top_pkg::FLASH_INFO_PER_BANK;  // Info pages per bank
  parameter int PagesPerBank = top_pkg::FLASH_PAGES_PER_BANK;  // Data pages per bank
  parameter int WordsPerPage = top_pkg::FLASH_WORDS_PER_PAGE;  // Number of bus words per page
  parameter int BusWidth = top_pkg::TL_DW;
  parameter int MpRegions = 8;  // flash controller protection regions
  parameter int FifoDepth = 16;  // rd / prog fifos

  // flash phy parameters
  parameter int DataByteWidth = $clog2(DataWidth / 8);
  parameter int BankW = $clog2(NumBanks);
  parameter int PageW = $clog2(PagesPerBank);
  parameter int WordW = $clog2(WordsPerPage);
  parameter int AddrW = BankW + PageW + WordW;  // all flash range
  parameter int BankAddrW = PageW + WordW;  // 1 bank of flash range
  parameter int AllPagesW = BankW + PageW;

  // flash ctrl / bus parameters
  // flash / bus width may be different from actual flash word width
  parameter int BusByteWidth = $clog2(BusWidth / 8);
  parameter int WidthMultiple = DataWidth / BusWidth;
  parameter int BusWordsPerPage = WordsPerPage * WidthMultiple;
  parameter int BusWordW = $clog2(BusWordsPerPage);
  parameter int BusAddrW = BankW + PageW + BusWordW;
  parameter int BusBankAddrW = PageW + BusWordW;
  parameter int PhyAddrStart = BusWordW - WordW;

  // fifo parameters
  parameter int FifoDepthW = $clog2(FifoDepth + 1);

  // Flash Operations Supported
  typedef enum logic [1:0] {
    FlashOpRead = 2'h0,
    FlashOpProgram = 2'h1,
    FlashOpErase = 2'h2,
    FlashOpInvalid = 2'h3
  } flash_op_e;

  // Flash Erase Operations Supported
  typedef enum logic {
    FlashErasePage = 0,
    FlashEraseBank = 1
  } flash_erase_e;

  parameter int EraseBitWidth = $bits(flash_erase_e);

  // Flash tlul to fifo direction
  typedef enum logic {
    WriteDir = 1'b0,
    ReadDir = 1'b1
  } flash_flfo_dir_e;

  // Flash partition type
  typedef enum logic {
    FlashPartData = 1'b0,
    FlashPartInfo = 1'b1
  } flash_part_e;

  // Flash controller to memory
  typedef struct packed {
    logic req;
    logic rd;
    logic prog;
    logic pg_erase;
    logic bk_erase;
    flash_part_e part;
    logic [BusAddrW-1:0] addr;
    logic [BusWidth-1:0] prog_data;
    logic prog_last;
    logic scramble_en;
    logic [127:0] addr_key;
    logic [127:0] data_key;
  } flash_req_t;

  // default value of flash_req_t (for dangling ports)
  parameter flash_req_t FLASH_REQ_DEFAULT
      = '{req: 1'b0, rd: 1'b0, prog: 1'b0, pg_erase: 1'b0, bk_erase: 1'b0,
          part: FlashPartData, addr: '0, prog_data: '0, prog_last: '0, scramble_en: '0, addr_key:
          128'hDEADBEEFBEEFFACEDEADBEEF5A5AA5A5, data_key: 128'hDEADBEEF5A5AA5A5DEADBEEFBEEFFACE};

  // memory to flash controller
  typedef struct packed {
    logic rd_done;
    logic prog_done;
    logic erase_done;
    logic [BusWidth-1:0] rd_data;
    logic init_busy;
  } flash_rsp_t;

  // default value of flash_rsp_t (for dangling ports)
  parameter flash_rsp_t FLASH_RSP_DEFAULT = '{rd_done: 1'b0, prog_done: 1'b0, erase_done: 1'b0,
                                              rd_data: '0, init_busy: 1'b0};

  ////////////////////////////
  // The following inter-module should be moved to OTP
  ////////////////////////////

  // otp to flash_phy
  typedef struct packed {
    logic [127:0] addr_key;
    logic [127:0] data_key;
  } otp_flash_t;

  // default value of otp_flash_t
  parameter otp_flash_t OTP_FLASH_DEFAULT = '{addr_key: 128'hDEADBEEFBEEFFACEDEADBEEF5A5AA5A5,
                                              data_key: 128'hDEADBEEF5A5AA5A5DEADBEEFBEEFFACE};



endpackage : flash_ctrl_pkg
