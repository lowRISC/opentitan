// Copyright lowRISC contributors (OpenTitan project).
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
  import flash_ctrl_prim_ral_pkg::*;
  import mem_bkdr_util_pkg::*;
  import prim_mubi_pkg::*;
  import lc_ctrl_pkg::*;
  import flash_phy_prim_agent_pkg::*;
  import sec_cm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = {"recov_err", "fatal_std_err", "fatal_err",
                                       "fatal_prim_flash_alert", "recov_prim_flash_alert"};

  // Some paths are added multiple times to accomodate
  // indexing in the loop
  parameter string LIST_OF_READ_SEED_FORCE_PATHS[] = {
    "tb.dut.u_flash_hw_if.op",
    "tb.dut.u_flash_hw_if.op",
    "tb.dut.u_flash_hw_if.part_sel",
    "tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd.data_i[31:0]",
    "tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd.data_i[31:0]"
  };

  parameter string LIST_OF_PROG_RMA_WIPE_FORCE_PATHS[] = {
    "tb.dut.u_eflash.gen_flash_cores[0].u_core.gen_prog_data.u_prog.data_i[31:0]",
    "tb.dut.u_eflash.gen_flash_cores[0].u_core.gen_prog_data.u_prog.data_i[31:0]",
    "tb.dut.u_flash_hw_if.rma_num_words"
  };

  parameter uint NUM_ALERTS = 5;
  parameter uint FlashNumPages = flash_ctrl_pkg::NumBanks * flash_ctrl_pkg::PagesPerBank;
  parameter uint FlashSizeBytes = FlashNumPages * flash_ctrl_pkg::WordsPerPage *
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
  parameter uint FlashIsolPartEndAddr   = 32'h00001FFF;

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
  parameter uint NumFlashErrBits  = 7;
  parameter uint FlashOpErr       = 0;
  parameter uint FlashMpErr       = 1;
  parameter uint FlashRdErr       = 2;
  parameter uint FlashProgErr     = 3;
  parameter uint FlashProgWinErr  = 4;
  parameter uint FlashProgTypeErr = 5;
  parameter uint FlashUpdateErr   = 6;

  // Flash STD Fault Bits (flash_ctrl.std_fault_status)
  parameter uint FlashStdFaultRegIntgErr   = 0;
  parameter uint FlashStdFaultProgIntgErr  = 1;
  parameter uint FlashStdFaultLcmgrErr     = 2;
  parameter uint FlashStdFaultLcmgrIntgErr = 3;
  parameter uint FlashStdFaultArbFsmErr    = 4;
  parameter uint FlashStdFaultStorageErr   = 5;
  parameter uint FlashStdFaultPhyFsmErr    = 6;
  parameter uint FlashStdFaultCtrlCntErr   = 7;
  parameter uint FlashStdFaultFifoErr      = 8;

  // Flash Fault Bits (flash_ctrl.fault_status)
  parameter uint FlashFaultOpErr         = 0;
  parameter uint FlashFaultMpErr         = 1;
  parameter uint FlashFaultRdErr         = 2;
  parameter uint FlashFaultProgErr       = 3;
  parameter uint FlashFaultProgWinErr    = 4;
  parameter uint FlashFaultProgTypeErr   = 5;
  parameter uint FlashFaultFlashMacroErr = 6;
  parameter uint FlashFaultSeedErr       = 7;
  parameter uint FlashFaultPhyRelblErr   = 8;
  parameter uint FlashFaultPhyStorageErr = 9;
  parameter uint FlashFaultSpuriousAck   = 10;
  parameter uint FlashFaultArbErr        = 11;
  parameter uint FlashFaultHostGntErr    = 12;

  // From flash_ctrl_lcmgr.sv
  parameter logic [10:0] FlashLcDisabled = 11'b11111100011;
  parameter logic [10:0] FlashLcInvalid  = 11'b11101011000;
  // types
  typedef enum bit [1:0] {
    OTFCfgTrue,
    OTFCfgFalse,
    OTFCfgRand
  } otf_cfg_mode_e;

  typedef enum {
    ReadCheckNorm = 0,
    ReadCheckRand = 1,
    ReadCheckErased = 2
  } read_check_e;

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
    FlashMemInitInvalidate, // Initialize with Xs.
    FlashMemInitEccMode     // Flash init for ecc_mode
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

  typedef enum {
    TgtRd = 0,
    TgtDr = 1, // direct read
    TgtWr = 2, // program
    TgtEr = 3, // erase
    NumTgt = 4
  } flash_tgt_prefix_e;

  typedef enum {
    FlashEccDisabled,
    FlashEccEnabled,
    FlashSerrTestMode,
    FlashDerrTestMode,
    FlashIerrTestMode
  } ecc_mode_e;

  typedef enum {
    ReadTaskCtrl = 0,
    ReadTaskHost = 1,
    NumReadTask  = 2
  } read_task_e;

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
  // Otf address in a bank.
  typedef bit [flash_ctrl_pkg::BusAddrByteW-FlashBankWidth-1 : 0] otf_addr_t;

  typedef struct packed {
    flash_dv_part_e  partition;   // data or one of the info partitions
    flash_erase_e    erase_type;  // erase page or the whole bank
    flash_op_e       op;          // read / program or erase
    flash_prog_sel_e prog_sel;    // program select: normal or repair
    uint             num_words;   // number of words to read or program (TL_DW)
    addr_t           addr;        // starting addr for the op
    // address for the ctrl interface per bank, 18:0
    bit [flash_ctrl_pkg::BusAddrByteW-2:0] otf_addr;
  } flash_op_t;

  // Address combined with region
  // Need for error injection.
  typedef struct packed {
    bit          bank;
    addr_t addr;
    flash_dv_part_e part;
  } rd_cache_t;

  parameter uint ALL_ZEROS = 32'h0000_0000;
  parameter uint ALL_ONES = 32'hffff_ffff;

  // Parameter for Probing into the DUT RMA FSM
  parameter string PRB_RMA_FSM = "tb.dut.u_flash_hw_if.state_q";

  // Taken from enum type lcmgr_state_e in flash_ctrl_lcmgr.sv
  parameter uint RMA_FSM_STATE_ST_RMA_RSP = 11'b10110001010;

  // Indicate host read
  parameter int unsigned OTFBankId = flash_ctrl_pkg::BusAddrByteW - FlashBankWidth; // bit19
  parameter int unsigned OTFHostId = OTFBankId - 1; // bit 18
  parameter int unsigned DVPageMSB = 18;
  parameter int unsigned DVPageLSB = 11;
  localparam int unsigned CtrlTransMin = 1;
  localparam int unsigned CtrlTransMax = 32;

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

  function automatic bit [FlashDataWidth-1:0] flash_gf_mult2(bit [FlashDataWidth-1:0] operand);
    bit [FlashDataWidth-1:0]          mult_out;

    mult_out = operand[FlashDataWidth-1] ? (operand << 1) ^
      flash_phy_pkg::ScrambleIPoly : (operand << 1);
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

  function automatic bit[63:0] create_flash_data(
           bit [FlashDataWidth-1:0] data, bit [FlashByteAddrWidth-1:0] byte_addr,
           bit [FlashKeySize-1:0]   flash_addr_key, bit [FlashKeySize-1:0] flash_data_key,
           bit dis = 1);
    bit [FlashAddrWidth-1:0]                                    word_addr;
    bit [FlashDataWidth-1:0]                                    mask;
    bit [FlashDataWidth-1:0]                                    masked_data;
    bit [FlashNumRoundsHalf-1:0][FlashDataWidth-1:0]            scrambled_data;

    // These parameters will be removed once it is included in mem_bkdr_util.sv
    int                                                         addr_lsb = 3;

    word_addr = byte_addr >> addr_lsb;
    mask = flash_galois_multiply(flash_addr_key, word_addr);
    masked_data = data ^ mask;
    crypto_dpi_prince_pkg::sv_dpi_prince_encrypt(.plaintext(masked_data), .key(flash_data_key),
                                             .old_key_schedule(0), .ciphertext(scrambled_data));
    masked_data = scrambled_data[FlashNumRoundsHalf-1] ^ mask;

    if (dis) begin
      `uvm_info("SCR_DBG", $sformatf("addr:%x  mask:%x  din:%x dout:%x",
                                     word_addr, mask, data, masked_data), UVM_MEDIUM)
    end
    return masked_data;
  endfunction

  // 64bit in out
  function automatic bit[FlashDataWidth-1:0] create_raw_data(
      input bit [FlashDataWidth-1:0]               data,
      input bit [FlashAddrWidth-1:0]               bank_addr,
      input bit [FlashKeySize-1:0]                 flash_addr_key,
      input bit [FlashKeySize-1:0]                 flash_data_key,
      input bit                                    dis = 1,
      input uvm_verbosity                          verbosity = UVM_MEDIUM);
    bit [FlashDataWidth-1:0]                         mask;
    bit [FlashDataWidth-1:0]                         masked_data;
    bit [FlashDataWidth-1:0]                         plain_text;
    bit [FlashNumRoundsHalf-1:0][FlashDataWidth-1:0] descrambled_data;

    mask = flash_galois_multiply(flash_addr_key, bank_addr);
    masked_data = data ^ mask;
    plain_text = crypto_dpi_prince_pkg::c_dpi_prince_decrypt(masked_data,
                                                             flash_data_key[127:64],
                                                             flash_data_key[63:0],
                                                             FlashNumRoundsHalf,
                                                             0);
    if (dis) begin
      `uvm_info("DCR_DBG", $sformatf("datakey:%x", flash_data_key), verbosity)
      `uvm_info("DCR_DBG", $sformatf("masked_data:%x cout:%x", masked_data, plain_text), verbosity)
      `uvm_info("DCR_DBG", $sformatf(
                "addr:%x  mask:%x  din:%x  dout:%x ",
                bank_addr, mask, data, (plain_text^mask)),
                verbosity)
    end

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

  function automatic flash_dv_part_e get_part_name(flash_phy_pkg::flash_phy_prim_flash_req_t req);
    flash_dv_part_e part;

    if (req.part == 0) return FlashPartData;
    else begin
      case(req.info_sel)
        0: begin
          return FlashPartInfo;
        end
        1: begin
          return FlashPartInfo1;
        end
        2: begin
          return FlashPartInfo2;
        end
        default: begin
          `uvm_error("get_partition_name", $sformatf("part:%0d info_sel:%0d doesn't exist",
                                                     req.part, req.info_sel))
        end
      endcase
    end

    `uvm_error("get_partition_name", $sformatf("part:%0d info_sel:%0d doesn't exist",
                                               req.part, req.info_sel))
    return FlashPartData;
  endfunction // get_part_name

  // Struct convertion from rtl to dv.
  function automatic flash_bank_mp_info_page_cfg_t conv2env_mp_info(info_page_cfg_t info);
    flash_bank_mp_info_page_cfg_t env_info;

    env_info.en    = info.en;
    env_info.read_en       = info.rd_en;
    env_info.program_en  = info.prog_en;
    env_info.erase_en      = info.erase_en;
    env_info.scramble_en = info.scramble_en;
    env_info.ecc_en        = info.ecc_en;
    env_info.he_en         = info.he_en;
    return env_info;
  endfunction

  function automatic void print_flash_op(input flash_op_t fop, uvm_verbosity verbosity);
    `uvm_info("print_flash_op", $sformatf(
              "flash_op: op=%s, part=%s, addr=0x%x, otf_addr=0x%x, words=%0d",
              fop.op.name, fop.partition.name, fop.addr, fop.otf_addr, fop.num_words),
              verbosity)
    if (fop.op == FlashOpErase) begin
      `uvm_info("print_flash_op", $sformatf(
                "flash_op: erase_type=%s", fop.erase_type.name), verbosity)
    end
  endfunction

  function automatic addr_t align_to_flash_word(addr_t addr);
     return {addr[$bits(addr_t) - 1 : FlashDataByteWidth], {FlashDataByteWidth{1'b0}}};
  endfunction

  // Round an address down to a program resolution window.
  function automatic addr_t round_to_prog_resolution(addr_t addr);
    return addr - (addr & (BusPgmResBytes - 1));
  endfunction

  // package sources
  `include "flash_mem_bkdr_util.sv"
  `include "flash_mem_addr_attrs.sv"
  `include "flash_otf_item.sv"
  `include "flash_otf_read_entry.sv"
  `include "flash_otf_mem_entry.sv"
  `include "flash_ctrl_seq_cfg.sv"
  `include "flash_ctrl_env_cfg.sv"
  `include "flash_ctrl_env_cov.sv"
  `include "flash_ctrl_virtual_sequencer.sv"
  `include "flash_ctrl_scoreboard.sv"
  `include "flash_ctrl_otf_scoreboard.sv"
  `include "flash_ctrl_env.sv"
  `include "flash_ctrl_vseq_list.sv"

endpackage
