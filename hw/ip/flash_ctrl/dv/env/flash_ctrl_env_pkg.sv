// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package flash_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_base_reg_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import flash_ctrl_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint FLASH_CTRL_ADDR_MAP_SIZE = 128;

  // TODO: These might be made into RTL design parameters.
  parameter FLASH_CTRL_NUM_BANKS                = top_pkg::FLASH_BANKS; // 2
  parameter FLASH_CTRL_NUM_PAGES_PER_BANK       = top_pkg::FLASH_PAGES_PER_BANK; // 256
  parameter FLASH_CTRL_NUM_PAGES                = FLASH_CTRL_NUM_BANKS *
                                                  FLASH_CTRL_NUM_PAGES_PER_BANK; // 512
  parameter FLASH_CTRL_NUM_INFO_PAGES_PER_BANK  = top_pkg::FLASH_INFO_PER_BANK; // 4
  parameter FLASH_CTRL_NUM_WORDS_PER_PAGE       = top_pkg::FLASH_WORDS_PER_PAGE; // 128
  parameter FLASH_CTRL_NUM_WORDS                = FLASH_CTRL_NUM_WORDS_PER_PAGE *
                                                  FLASH_CTRL_NUM_PAGES;
  parameter FLASH_CTRL_WORD_SIZE_BYTES          = top_pkg::FLASH_DATA_WIDTH / 8; // 8
  parameter FLASH_CTRL_NUM_BUS_WORDS            = FLASH_CTRL_NUM_WORDS *
                                                  FLASH_CTRL_WORD_SIZE_BYTES /
                                                  top_pkg::TL_DBW;
  parameter FLASH_CTRL_PAGE_NUM_BUS_WORDS       = FLASH_CTRL_NUM_WORDS_PER_PAGE *
                                                  FLASH_CTRL_WORD_SIZE_BYTES /
                                                  top_pkg::TL_DBW;
  parameter FLASH_CTRL_BANK_NUM_BUS_WORDS       = FLASH_CTRL_PAGE_NUM_BUS_WORDS *
                                                  FLASH_CTRL_NUM_PAGES_PER_BANK;
  parameter FLASH_CTRL_SIZE_BYTES               = FLASH_CTRL_WORD_SIZE_BYTES *
                                                  FLASH_CTRL_NUM_WORDS_PER_PAGE *
                                                  FLASH_CTRL_NUM_PAGES;
  parameter FLASH_CTRL_NUM_MP_REGIONS           = 8;
  parameter FLASH_CTRL_FIFO_DEPTH               = 16; // prog or rd fifo

  // helper params
  localparam FLASH_CTRL_MEM_ADDR_WORD_MSB       = $clog2(FLASH_CTRL_WORD_SIZE_BYTES) - 1;
  localparam FLASH_CTRL_MEM_ADDR_WORD_LINE_MSB  = FLASH_CTRL_MEM_ADDR_WORD_MSB +
                                                  $clog2(FLASH_CTRL_NUM_WORDS_PER_PAGE);
  localparam FLASH_CTRL_MEM_ADDR_PAGE_MSB       = FLASH_CTRL_MEM_ADDR_WORD_LINE_MSB +
                                                  $clog2(FLASH_CTRL_NUM_PAGES_PER_BANK);
  localparam FLASH_CTRL_MEM_ADDR_BANK_MSB       = FLASH_CTRL_MEM_ADDR_PAGE_MSB +
                                                  $clog2(FLASH_CTRL_NUM_BANKS);

  // types
  typedef enum int {
    FlashCtrlIntrProgEmpty  = 0,
    FlashCtrlIntrProgLvl    = 1,
    FlashCtrlIntrRdFull     = 2,
    FlashCtrlIntrRdLvl      = 3,
    FlashCtrlIntrOpDone     = 4,
    FlashCtrlIntrOpError    = 5,
    NumFlashCtrlIntr        = 6
  } flash_ctrl_intr_e;

  typedef enum {
    FlashMemInitCustom,     // Initialize flash (via bkdr) with custom data set.
    FlashMemInitSet,        // Initialize with all 1s.
    FlashMemInitClear,      // Initialize with all 0s.
    FlashMemInitRandomize,  // Initialize with random data.
    FlashMemInitInvalidate  // Initialize with Xs.
  } flash_mem_init_e;

  typedef enum bit [1:0] {
    FlashCtrlOpRead,
    FlashCtrlOpProgram,
    FlashCtrlOpErase,
    FlashCtrlOpInvalid
  } flash_ctrl_op_e;

  typedef enum bit {
    FlashCtrlErasePage,
    FlashCtrlEraseBank
  } flash_ctrl_erase_e;

  typedef enum bit {
    FlashCtrlPartitionData,
    FlashCtrlPartitionInfo
  } flash_ctrl_partition_e;

  typedef struct packed {
    bit   en;                         // enable this region
    bit   read_en;                    // enable reads
    bit   program_en;                 // enable write
    bit   erase_en;                   // enable erase
    flash_ctrl_partition_e partition; // info or data
    uint  num_pages;                  // 0:FLASH_CTRL_NUM_PAGES-1 % start_page
    uint  start_page;                 // 0:FLASH_CTRL_NUM_PAGES-1
  } flash_ctrl_mp_region_t;

  typedef struct packed {
    flash_ctrl_partition_e  partition;  // data or info partition
    flash_ctrl_erase_e      erase_type; // erase page or the whole bank
    flash_ctrl_op_e         op;         // read / program or erase
    uint                    num_words;  // number of words to read or program (TL_DW)
    bit [TL_AW-1:0]         addr;       // starting addr for the op
  } flash_ctrl_single_op_t;

  typedef virtual mem_bkdr_if mem_bkdr_vif;

  // functions

  // package sources
  `include "flash_mem_addr_attrs.sv"
  `include "flash_ctrl_seq_cfg.sv"
  `include "flash_ctrl_env_cfg.sv"
  `include "flash_ctrl_env_cov.sv"
  `include "flash_ctrl_virtual_sequencer.sv"
  `include "flash_ctrl_scoreboard.sv"
  `include "flash_ctrl_env.sv"
  `include "flash_ctrl_vseq_list.sv"

endpackage
