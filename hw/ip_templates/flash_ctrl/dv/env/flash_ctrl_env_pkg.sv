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
  import flash_ctrl_pkg::*;
  import flash_ctrl_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = {"recov_err", "recov_mp_err", "recov_ecc_err"};
  parameter uint NUM_ALERTS = 3;
  parameter uint FlashNumPages            = flash_ctrl_pkg::NumBanks * flash_ctrl_pkg::PagesPerBank;
  parameter uint FlashSizeBytes           = FlashNumPages * flash_ctrl_pkg::WordsPerPage *
                                            flash_ctrl_pkg::DataWidth / 8;

  parameter uint FlashNumBusWords         = FlashSizeBytes / top_pkg::TL_DBW;
  parameter uint FlashNumBusWordsPerBank  = FlashNumBusWords / flash_ctrl_pkg::NumBanks;
  parameter uint FlashNumBusWordsPerPage  = FlashNumBusWordsPerBank / flash_ctrl_pkg::PagesPerBank;

  parameter uint FlashBankBytesPerWord    = flash_ctrl_pkg::DataWidth / 8;

  parameter uint FlashDataByteWidth       = $clog2(FlashBankBytesPerWord);
  parameter uint FlashWordLineWidth       = $clog2(flash_ctrl_pkg::WordsPerPage);
  parameter uint FlashPageWidth           = $clog2(flash_ctrl_pkg::PagesPerBank);
  parameter uint FlashBankWidth           = $clog2(flash_ctrl_pkg::NumBanks);
  parameter uint FlashPgmRes              = flash_ctrl_pkg::BusPgmRes;
  parameter uint FlashPgmResWidth         = $clog2(FlashPgmRes);

  parameter uint FlashMemAddrWordMsbBit   = FlashDataByteWidth - 1;
  parameter uint FlashMemAddrLineMsbBit   = FlashDataByteWidth + FlashWordLineWidth - 1;
  parameter uint FlashMemAddrPageMsbBit   = FlashDataByteWidth + FlashWordLineWidth +
                                            FlashPageWidth - 1;
  parameter uint FlashMemAddrBankMsbBit   = FlashDataByteWidth + FlashWordLineWidth +
                                            FlashPageWidth + FlashBankWidth - 1;

  // types
  typedef enum int {
    FlashCtrlIntrProgEmpty  = 0,
    FlashCtrlIntrProgLvl    = 1,
    FlashCtrlIntrRdFull     = 2,
    FlashCtrlIntrRdLvl      = 3,
    FlashCtrlIntrOpDone     = 4,
    NumFlashCtrlIntr        = 5
  } flash_ctrl_intr_e;

  typedef enum {
    FlashMemInitCustom,     // Initialize flash (via bkdr) with custom data set.
    FlashMemInitSet,        // Initialize with all 1s.
    FlashMemInitClear,      // Initialize with all 0s.
    FlashMemInitRandomize,  // Initialize with random data.
    FlashMemInitInvalidate  // Initialize with Xs.
  } flash_mem_init_e;

  // Partition select for DV
  typedef enum logic [flash_ctrl_pkg::InfoTypes:0] { // Data partition and all info partitions
    FlashPartData  = 0,
    FlashPartInfo  = 1,
    FlashPartInfo1 = 2,
    FlashPartRed   = 4
  } flash_dv_part_e;

  typedef struct packed {
    bit           en;         // enable this region
    bit           read_en;    // enable reads
    bit           program_en; // enable write
    bit           erase_en;   // enable erase
    flash_part_e  partition;  // info or data
    uint          num_pages;  // 0:NumPages % start_page
    uint          start_page; // 0:NumPages-1
  } flash_mp_region_cfg_t;

  typedef struct packed {
    flash_dv_part_e partition;  // data or one of the info partitions
    flash_erase_e   erase_type; // erase page or the whole bank
    flash_op_e      op;         // read / program or erase
    uint            num_words;  // number of words to read or program (TL_DW)
    bit [TL_AW-1:0] addr;       // starting addr for the op
  } flash_op_t;

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
