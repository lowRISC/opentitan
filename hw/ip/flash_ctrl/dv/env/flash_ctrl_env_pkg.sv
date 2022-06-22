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
  import flash_phy_prim_agent_pkg::*;
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

  // params for words
  parameter uint NUM_PAGE_WORDS = FlashNumBusWordsPerPage;
  parameter uint NUM_BK_DATA_WORDS = FlashNumBusWordsPerBank;  // 256 pages
  parameter uint NUM_BK_INFO_WORDS = InfoTypeBusWords[0];  // 10 pages

  // params for num of pages
  parameter uint NUM_PAGE_PART_DATA = flash_ctrl_pkg::PagesPerBank;
  parameter uint NUM_PAGE_PART_INFO0 = flash_ctrl_pkg::InfoTypeSize[0];
  parameter uint NUM_PAGE_PART_INFO1 = flash_ctrl_pkg::InfoTypeSize[1];
  parameter uint NUM_PAGE_PART_INFO2 = flash_ctrl_pkg::InfoTypeSize[2];

  parameter otp_ctrl_pkg::flash_otp_key_rsp_t FLASH_OTP_RSP_DEFAULT = '{
      data_ack: 1'b1,
      addr_ack: 1'b1,
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

  // MP Access Flags
  parameter bit MP_PASS      = 0;
  parameter bit MP_VIOLATION = 1;

  // Flash Error Bits (flash_ctrl.err_code)
  parameter uint NumFlashErrBits  = 8;
  parameter uint FlashOpErr       = 0;
  parameter uint FlashMpErr       = 1;
  parameter uint FlashRdErr       = 2;
  parameter uint FlashProgErr     = 3;
  parameter uint FlashProgWinErr  = 4;
  parameter uint FlashProgTypeErr = 5;
  parameter uint FlashMacroErr    = 6;
  parameter uint FlashUpdateErr   = 7;

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
    FlashPartData  = 0,
    FlashPartInfo  = 1,
    FlashPartInfo1 = 2,
    FlashPartInfo2 = 4
  } flash_dv_part_e;

  // Program Type Select Normal/Repair
  typedef enum bit {
    FlashProgSelNormal = 0,
    FlashProgSelRepair = 1
  } flash_prog_sel_e;

  // Special Partitions
  typedef enum logic [2:0] {
    FlashCreatorPart = 0,
    FlashOwnerPart   = 1,
    FlashIsolPart    = 2,
    FlashData0Part   = 3,
    FlashData1Part   = 4
  } flash_sec_part_e;

  typedef enum {
    AllOnes,   // All 1s
    AllZeros,  // All 0s
    CustomVal  // Custom Value
  } flash_scb_wr_e;

  typedef struct packed {
    mubi4_t en;           // enable this region
    mubi4_t read_en;      // enable reads
    mubi4_t program_en;   // enable write
    mubi4_t erase_en;     // enable erase
    mubi4_t scramble_en;  // enable scramble
    mubi4_t ecc_en;       // enable ecc
    mubi4_t he_en;        // enable high endurance
    uint    num_pages;    // 0:NumPages % start_page
    uint    start_page;   // 0:NumPages-1
  } flash_mp_region_cfg_t;

  typedef struct packed {
    mubi4_t en;           // enable this page
    mubi4_t read_en;      // enable reads
    mubi4_t program_en;   // enable write
    mubi4_t erase_en;     // enable erase
    mubi4_t scramble_en;  // enable scramble
    mubi4_t ecc_en;       // enable ecc
    mubi4_t he_en;        // enable high endurance
  } flash_bank_mp_info_page_cfg_t;

  // 2-states flash data type
  typedef bit [TL_DW-1:0] data_t;
  // 4-states flash data type
  typedef logic [TL_DW-1:0] data_4s_t;
  // flash address type
  typedef bit [TL_AW-1:0] addr_t;
  // Queue of 4-states data words
  typedef data_4s_t data_q_t[$];
  // Queue of 2-states data words
  typedef data_t data_b_t[$];
  // Array of 2-states data words indexed with flash addresses.
  // Useful for the flash model.
  typedef data_t data_model_t[addr_t];

  typedef struct packed {
    flash_dv_part_e  partition;   // data or one of the info partitions
    flash_erase_e    erase_type;  // erase page or the whole bank
    flash_op_e       op;          // read / program or erase
    flash_prog_sel_e prog_sel;    // program select
    uint             num_words;   // number of words to read or program (TL_DW)
    addr_t           addr;        // starting addr for the op
    // addres for the ctrl interface per bank, 18:0
    bit [flash_ctrl_pkg::BusAddrByteW-2:0] otf_addr;
  } flash_op_t;

  parameter uint ALL_ZEROS = 32'h0000_0000;
  parameter uint ALL_ONES = 32'hffff_ffff;

  // Parameter for Probing into the DUT RMA FSM
  parameter string PRB_RMA_FSM = "tb.dut.u_flash_hw_if.state_q";
  // Taken from enum type lcmgr_state_e in flash_ctrl_lcmgr.sv
  parameter uint RMA_FSM_STATE_ST_RMA_RSP = 11'b10110001010;

  // Indicate host read
  parameter int unsigned OTFBankId = flash_ctrl_pkg::BusAddrByteW - 1; // bit19
  parameter int unsigned OTFHostId = OTFBankId - 1; // bit 18
  localparam int unsigned CTRL_TRANS_MIN = 1;
  localparam int unsigned CTRL_TRANS_MAX = 32;

  // functions
  // Add below for the temporary until PR12492 is merged.
  // Will be removed after.
  localparam int unsigned FlashDataWidth = flash_phy_pkg::DataWidth;
  localparam int unsigned FlashStagesPerCycle = FlashDataWidth / flash_phy_pkg::GfMultCycles;
  localparam int unsigned FlashKeySize = flash_phy_pkg::KeySize;
  localparam int unsigned FlashNumRoundsHalf = crypto_dpi_prince_pkg::NumRoundsHalf;
  localparam int unsigned FlashAddrWidth = 16;

  // remove bank select
  localparam int unsigned FlashByteAddrWidth = flash_ctrl_pkg::BusAddrByteW - 1;

  localparam bit [FlashDataWidth-1:0] IPoly = FlashDataWidth'(1'b1) << 15 |
                                      FlashDataWidth'(1'b1) << 9  |
                                      FlashDataWidth'(1'b1) << 7  |
                                      FlashDataWidth'(1'b1) << 4  |
                                      FlashDataWidth'(1'b1) << 3  |
                                      FlashDataWidth'(1'b1) << 0;

  function automatic bit [FlashDataWidth-1:0] flash_gf_mult2(bit [FlashDataWidth-1:0] operand);
    bit [FlashDataWidth-1:0]          mult_out;

    mult_out = operand[FlashDataWidth-1] ? (operand << 1) ^ IPoly : (operand << 1);
    return mult_out;
  endfunction

  function automatic bit [FlashStagesPerCycle-1:0][FlashDataWidth-1:0] flash_gen_matrix(
                                      bit [FlashDataWidth-1:0] seed, bit init);
    bit [FlashStagesPerCycle-1:0][FlashDataWidth-1:0] matrix_out;

    matrix_out[0] = init ? seed : flash_gf_mult2(seed);
    matrix_out[FlashStagesPerCycle-1:1] = '0;
    for (int i = 1; i < FlashStagesPerCycle; i++) begin
      matrix_out[i] = flash_gf_mult2(matrix_out[i-1]);
    end
    return matrix_out;
  endfunction

  function automatic bit [FlashDataWidth-1:0] flash_galois_multiply(bit [FlashKeySize-1:0] addr_key,
                                                          bit [FlashAddrWidth-1:0] addr);
    bit [FlashStagesPerCycle-1:0][FlashDataWidth-1:0]                              matrix[2];
    bit [FlashDataWidth-1:0]                                                       product[2];
    bit [FlashDataWidth-1:0]                                                       add_vector;
    bit [FlashDataWidth-1:0]                                                       mult_out;

    // generate matrix.
    matrix[0] =
      flash_gen_matrix({addr_key[FlashKeySize-FlashAddrWidth-1:FlashKeySize-64], addr}, 1'b1);
    matrix[1] = flash_gen_matrix(matrix[0][FlashStagesPerCycle-1], 1'b0);
    `uvm_info("SCR_DBG", $sformatf("waddr: %x   op_a_i : %x     vector: %x",
              addr,  {addr_key[FlashKeySize-FlashAddrWidth-1:FlashKeySize-64], addr},
              matrix[0][FlashStagesPerCycle-1]), UVM_HIGH)

    // galois multiply.
    for (int j = 0; j < 2; j++) begin
      mult_out = '0;
      for (int i = 0; i < FlashStagesPerCycle; i++) begin
        add_vector = addr_key[(j*FlashStagesPerCycle)+i] ? matrix[j][i] : '0;
        mult_out   = mult_out ^ add_vector;
      end
      product[j] = mult_out;
    end
    product[1] = product[1] ^ product[0];
    `uvm_info("SCR_DBG", $sformatf("prod1:%x   prod0:%x",product[1],product[0]), UVM_HIGH)

    return product[1];
  endfunction

  function automatic bit[75:0] create_flash_data(
           bit [FlashDataWidth-1:0] data, bit [FlashByteAddrWidth-1:0] byte_addr,
           bit [FlashKeySize-1:0]   flash_addr_key, bit [FlashKeySize-1:0] flash_data_key);
    bit [FlashAddrWidth-1:0]                                    word_addr;
    bit [FlashDataWidth-1:0]                                    mask;
    bit [FlashDataWidth-1:0]                                    masked_data;
    bit [FlashNumRoundsHalf-1:0][FlashDataWidth-1:0]            scrambled_data;
    bit [71:0]                                                  ecc_72;
    bit [75:0]                                                  ecc_76;

    // These parameters will be removed once it is included in mem_bkdr_util.sv
    int                                                         addr_lsb = 3;

    word_addr = byte_addr >> addr_lsb;
    mask = flash_galois_multiply(flash_addr_key, word_addr);
    masked_data = data ^ mask;
    `uvm_info("SCR_DBG", $sformatf("addr:%x  mask:%x  data:%x", word_addr, mask, data), UVM_HIGH)
    crypto_dpi_prince_pkg::sv_dpi_prince_encrypt(.plaintext(masked_data), .key(flash_data_key),
                                             .old_key_schedule(0), .ciphertext(scrambled_data));

    masked_data = scrambled_data[FlashNumRoundsHalf-1] ^ mask;
    // ecc functions used are hardcoded to a fixed sized.
    ecc_72 = prim_secded_pkg::prim_secded_hamming_72_64_enc(data[63:0]);
    ecc_76 = prim_secded_pkg::prim_secded_hamming_76_68_enc({ecc_72[67:64], masked_data[63:0]});
    return ecc_76;
  endfunction

  function automatic bit[FlashDataWidth-1:0] create_raw_data(
      input bit [flash_phy_pkg::FullDataWidth-1:0] data,
      input bit [FlashAddrWidth-1:0]     bank_addr,
      input bit [FlashKeySize-1:0]       flash_addr_key,
      input bit [FlashKeySize-1:0]       flash_data_key,
      output bit [1:0]                   ecc_72_err,
      output bit [1:0]                   ecc_76_err);
    bit [FlashDataWidth-1:0]                         mask;
    bit [FlashDataWidth-1:0]                         masked_data;
    bit [FlashDataWidth-1:0]                         plain_text;
    prim_secded_pkg::secded_hamming_76_68_t          dec68;
    bit [FlashNumRoundsHalf-1:0][FlashDataWidth-1:0] descrambled_data;

    mask = flash_galois_multiply(flash_addr_key, bank_addr);

    // TODO supprot ecc
    //dec68 = prim_secded_pkg::prim_secded_hamming_76_68_dec(data);
    dec68.data = data;
    masked_data = dec68.data[FlashDataWidth-1:0] ^ mask;

    plain_text = crypto_dpi_prince_pkg::c_dpi_prince_decrypt(masked_data,
                                                             flash_data_key[127:64],
                                                             flash_data_key[63:0],
                                                             FlashNumRoundsHalf,
                                                             0);

    `uvm_info("SCR_DBG", $sformatf(
              "addr:%x  mask:%x  indata:%x  masked_data:%x  cipher_o:%x  finaldata:%x",
              bank_addr, mask, data, masked_data, plain_text, (plain_text^mask)),
              UVM_HIGH)

    ecc_76_err = dec68.err;
    return (plain_text ^ mask);
  endfunction // create_raw_data

  // Temp add end
  // Print 16 byte per line
  function automatic void flash_otf_print_data64(data_q_t data, string str = "data");
    int size, tail, line, idx;
    bit [127:0] vec;
    size = data.size();
    line = size / 4;
    tail = size % 4;
    idx = 0;
    `dv_info($sformatf("size : %0d byte (%0d x 4B)", (size * 4),  size), UVM_MEDIUM, str)

    for (int i = 0; i < line; ++i) begin
      for (int j = 0; j < 4; ++j) begin
        vec[127-(32*j) -:32] = data[idx];
        idx++;
      end
      `dv_info($sformatf("%4d:%8x_%8x_%8x_%8x", i,
                         vec[127:96], vec[95:64], vec[63:32], vec[31:0]),
               UVM_MEDIUM, str)
      vec = 'h0;
    end

    if (tail > 0) begin
      // print tail
      for (int j = 0; j < tail; ++j) begin
        vec[127-(32*j) -:32] = data[idx];
        idx++;
      end
      `dv_info($sformatf("%4d:%8x_%8x_%8x_%8x", line,
                         vec[127:96], vec[95:64], vec[63:32], vec[31:0]),
               UVM_MEDIUM, str)
    end
  endfunction // flash_otf_print_data64

  // package sources
  `include "flash_mem_bkdr_util.sv"
  `include "flash_mem_addr_attrs.sv"
  `include "flash_otf_item.sv"
  `include "flash_ctrl_seq_cfg.sv"
  `include "flash_ctrl_env_cfg.sv"
  `include "flash_ctrl_env_cov.sv"
  `include "flash_ctrl_virtual_sequencer.sv"
  `include "flash_ctrl_scoreboard.sv"
  `include "flash_ctrl_otf_scoreboard.sv"
  `include "flash_ctrl_env.sv"
  `include "flash_ctrl_vseq_list.sv"

endpackage
