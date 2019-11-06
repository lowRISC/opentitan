// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Faux Flash Controller module.
//

package flash_ctrl_pkg;

  localparam int FlashTotalPages = top_pkg::FLASH_BANKS * top_pkg::FLASH_PAGES_PER_BANK;
  localparam int AllPagesW = $clog2(FlashTotalPages);

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
    logic                         req;
    logic                         rd;
    logic                         prog;
    logic                         pg_erase;
    logic                         bk_erase;
    logic [top_pkg::FLASH_AW-1:0] addr;
    logic [top_pkg::FLASH_DW-1:0] prog_data;
  } flash_c2m_t;

  // memory to flash controller
  typedef struct packed {
    logic                         rd_done;
    logic                         prog_done;
    logic                         erase_done;
    logic [top_pkg::FLASH_DW-1:0] rd_data;
    logic                         init_busy;
  } flash_m2c_t;

endpackage : flash_ctrl_pkg
