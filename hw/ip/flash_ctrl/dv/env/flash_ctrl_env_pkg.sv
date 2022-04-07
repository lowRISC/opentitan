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
  import flash_ctrl_core_ral_pkg::*;
  import flash_ctrl_eflash_ral_pkg::*;
  import mem_bkdr_util_pkg::*;
  import prim_mubi_pkg::*;
  import lc_ctrl_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = {"recov_err", "fatal_std_err", "fatal_err"};

  parameter uint NUM_ALERTS = 3;
  parameter uint FlashNumPages = flash_ctrl_pkg::NumBanks * flash_ctrl_pkg::PagesPerBank;
  parameter uint FlashSizeBytes         = FlashNumPages * flash_ctrl_pkg::WordsPerPage *
                                            flash_ctrl_pkg::DataWidth / 8;

  parameter uint ProgFifoDepth = 4;
  parameter uint ReadFifoDepth = 16;

  // Number of bytes in each of the flash pages.
  parameter uint BytesPerPage = FlashSizeBytes / FlashNumPages;

  // Num of bytes in each of the flash banks for each of the flash partitions.
  parameter uint BytesPerBank = FlashSizeBytes / flash_ctrl_pkg::NumBanks;

  parameter uint InfoTypeBytes[flash_ctrl_pkg::InfoTypes] = '{
      flash_ctrl_pkg::InfoTypeSize[0] * BytesPerPage,
      flash_ctrl_pkg::InfoTypeSize[1] * BytesPerPage,
      flash_ctrl_pkg::InfoTypeSize[2] * BytesPerPage
  };

  parameter uint FlashNumBusWords = FlashSizeBytes / top_pkg::TL_DBW;
  parameter uint FlashNumBusWordsPerBank = FlashNumBusWords / flash_ctrl_pkg::NumBanks;
  parameter uint FlashNumBusWordsPerPage = FlashNumBusWordsPerBank / flash_ctrl_pkg::PagesPerBank;

  parameter uint InfoTypeBusWords[flash_ctrl_pkg::InfoTypes] = '{
      flash_ctrl_pkg::InfoTypeSize[0] * FlashNumBusWordsPerPage,
      flash_ctrl_pkg::InfoTypeSize[1] * FlashNumBusWordsPerPage,
      flash_ctrl_pkg::InfoTypeSize[2] * FlashNumBusWordsPerPage
  };

  parameter uint FlashBankBytesPerWord = flash_ctrl_pkg::DataWidth / 8;

  parameter uint FlashDataByteWidth = $clog2(FlashBankBytesPerWord);
  parameter uint FlashWordLineWidth = $clog2(flash_ctrl_pkg::WordsPerPage);
  parameter uint FlashPageWidth = $clog2(flash_ctrl_pkg::PagesPerBank);
  parameter uint FlashBankWidth = $clog2(flash_ctrl_pkg::NumBanks);
  parameter uint FlashPgmRes = flash_ctrl_pkg::BusPgmRes;
  parameter uint FlashPgmResWidth = $clog2(FlashPgmRes);

  parameter uint FlashMemAddrWordMsbBit = FlashDataByteWidth - 1;
  parameter uint FlashMemAddrLineMsbBit = FlashDataByteWidth + FlashWordLineWidth - 1;
  parameter uint FlashMemAddrPageMsbBit   = FlashDataByteWidth + FlashWordLineWidth +
                                            FlashPageWidth - 1;
  parameter uint FlashMemAddrBankMsbBit   = FlashDataByteWidth + FlashWordLineWidth +
                                            FlashPageWidth + FlashBankWidth - 1;
  // Need to create a design parameter for this
  parameter uint FlashFullDataWidth = flash_ctrl_pkg::DataWidth + 4;

  // params for words
  parameter uint NUM_PAGE_WORDS            = 512;
  parameter uint NUM_BK_DATA_WORDS         = 131072; // 256 pages
  parameter uint NUM_BK_INFO_WORDS         = 5120;   // 10 pages

  // params for num of pages
  parameter uint NUM_PAGE_PART_DATA        = 512;
  parameter uint NUM_PAGE_PART_INFO0       = 10;

  parameter otp_ctrl_pkg::flash_otp_key_rsp_t FLASH_OTP_RSP_DEFAULT = '{
      data_ack: 1'b0,
      addr_ack: 1'b0,
      key: '0,
      rand_key: '0,
      seed_valid: 1'b0
  };

  // For Secret Partitions and RMA
  parameter uint FlashSecretPartWords = 8;  // Size Of Secret Part - (8x32=256 Bits)
  parameter uint FlashCreatorPartStartAddr = 32'h00000800;  // Info Partition Page 1
  parameter uint FlashOwnerPartStartAddr = 32'h00001000;  // Info Partition Page 2
  parameter uint FlashIsolPartStartAddr = 32'h00001800;

  parameter uint FlashData0StartAddr = 32'h00000000;
  parameter uint FlashData0EndAddr = 32'h00080000;
  parameter uint FlashData1StartAddr = 32'h00080000;
  parameter uint FlashData1EndAddr = 32'h00100000;

  parameter uint FullPageNumWords = 512;  // 32 Cycles of 16 Words = 512 Words
  parameter uint FullBankNumWords = 131072;  // 8192 Cycles of 16 Words = 131072 Words

  parameter uint MaxNumPages = 256;  // Number of Pages in a Bank
  parameter uint FIFO_DEPTH = 16;  // Depth of the Program and Read FIFO in words

  // Read Check Parameters
  parameter bit READ_CHECK_NORM = 0;  // Check Read Data via the Backdoor
  parameter bit READ_CHECK_EXPLICIT = 1;  // Check Read Data Explicitly

  // Code Fetch Key
  parameter uint CODE_EXEC_KEY_W = 32;
  parameter uint CODE_EXEC_KEY = 32'ha26a38f7;

  // types
  typedef enum int {
    FlashCtrlIntrProgEmpty = 0,
    FlashCtrlIntrProgLvl   = 1,
    FlashCtrlIntrRdFull    = 2,
    FlashCtrlIntrRdLvl     = 3,
    FlashCtrlIntrOpDone    = 4,
    FlashCtrlIntrErr       = 5,
    NumFlashCtrlIntr       = 6
  } flash_ctrl_intr_e;

  typedef enum {
    FlashMemInitCustom,     // Initialize flash (via bkdr) with custom data set.
    FlashMemInitSet,        // Initialize with all 1s.
    FlashMemInitClear,      // Initialize with all 0s.
    FlashMemInitRandomize,  // Initialize with random data.
    FlashMemInitInvalidate  // Initialize with Xs.
  } flash_mem_init_e;

  // Partition select for DV
  typedef enum logic [flash_ctrl_pkg::InfoTypes:0] {  // Data partition and all info partitions
    FlashPartData       = 0,
    FlashPartInfo       = 1,
    FlashPartInfo1      = 2,
    FlashPartInfo2      = 4
  } flash_dv_part_e;

  // Special Partitions
  typedef enum logic [2:0] {
    FlashCreatorPart = 0,
    FlashOwnerPart   = 1,
    FlashIsolPart    = 2,
    FlashData0Part   = 3,
    FlashData1Part   = 4
  } flash_sec_part_e;

  typedef struct packed {
    bit  en;           // enable this region
    bit  read_en;      // enable reads
    bit  program_en;   // enable write
    bit  erase_en;     // enable erase
    bit  scramble_en;  // enable scramble
    bit  ecc_en;       // enable ecc
    bit  he_en;        // enable high endurance
    uint num_pages;    // 0:NumPages % start_page
    uint start_page;   // 0:NumPages-1
  } flash_mp_region_cfg_t;

  typedef struct packed {
    bit en;           // enable this page
    bit read_en;      // enable reads
    bit program_en;   // enable write
    bit erase_en;     // enable erase
    bit scramble_en;  // enable scramble
    bit ecc_en;       // enable ecc
    bit he_en;        // enable high endurance
  } flash_bank_mp_info_page_cfg_t;

  typedef struct packed {
    flash_dv_part_e partition;   // data or one of the info partitions
    flash_erase_e   erase_type;  // erase page or the whole bank
    flash_op_e      op;          // read / program or erase
    uint            num_words;   // number of words to read or program (TL_DW)
    bit [TL_AW-1:0] addr;        // starting addr for the op
  } flash_op_t;

  // Data queue for flash transactions
  typedef logic [TL_DW-1:0] data_q_t[$];
  typedef bit [TL_DW-1:0] data_t;
  typedef bit [TL_AW-1:0] addr_t;

  // Parameter for Probing into the DUT RMA FSM
  parameter string PRB_RMA_FSM = "tb.dut.u_flash_hw_if.state_q";
  // Taken from enum type lcmgr_state_e in flash_ctrl_lcmgr.sv
  parameter uint RMA_FSM_STATE_ST_RMA_RSP = 11'b10100100001;

  // functions

  // package sources
  `include "flash_mem_bkdr_util.sv"
  `include "flash_mem_addr_attrs.sv"
  `include "flash_ctrl_seq_cfg.sv"
  `include "flash_ctrl_env_cfg.sv"
  `include "flash_ctrl_env_cov.sv"
  `include "flash_ctrl_virtual_sequencer.sv"
  `include "flash_ctrl_scoreboard.sv"
  `include "flash_ctrl_env.sv"
  `include "flash_ctrl_vseq_list.sv"

endpackage
