// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package otp_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import dv_base_reg_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import push_pull_agent_pkg::*;
  import otp_ctrl_ral_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_pkg::*;
  import otp_ctrl_part_pkg::*;
  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[]      = {"fatal_macro_error", "fatal_check_error"};
  parameter uint NUM_ALERTS              = 2;

  parameter uint DIGEST_SIZE             = 8;
  parameter uint SW_WINDOW_BASE_ADDR     = 'h1000;
  parameter uint TEST_ACCESS_BASE_ADDR   = 'h2000;
  parameter uint SW_WINDOW_SIZE          = 512 * 4;
  parameter uint TEST_ACCESS_WINDOW_SIZE = 16 * 4;

  // convert byte into TLUL width size
  parameter uint CREATOR_SW_CFG_START_ADDR  = CreatorSwCfgOffset / (TL_DW / 8);
  parameter uint CREATOR_SW_CFG_DIGEST_ADDR = CreatorSwCfgDigestOffset / (TL_DW / 8);
  parameter uint CREATOR_SW_CFG_END_ADDR    = CREATOR_SW_CFG_DIGEST_ADDR - 1;

  parameter uint OWNER_SW_CFG_START_ADDR  = OwnerSwCfgOffset / (TL_DW / 8);
  parameter uint OWNER_SW_CFG_DIGEST_ADDR = OwnerSwCfgDigestOffset / (TL_DW / 8);
  parameter uint OWNER_SW_CFG_END_ADDR    = OWNER_SW_CFG_DIGEST_ADDR - 1;

  parameter uint HW_CFG_START_ADDR  = HwCfgOffset / (TL_DW / 8);
  parameter uint HW_CFG_DIGEST_ADDR = HwCfgDigestOffset / (TL_DW / 8);
  parameter uint HW_CFG_END_ADDR    = HW_CFG_DIGEST_ADDR - 1;

  parameter uint SECRET0_START_ADDR  = Secret0Offset / (TL_DW / 8);
  parameter uint SECRET0_DIGEST_ADDR = Secret0DigestOffset / (TL_DW / 8);
  parameter uint SECRET0_END_ADDR    = SECRET0_DIGEST_ADDR - 1;

  parameter uint SECRET1_START_ADDR  = Secret1Offset / (TL_DW / 8);
  parameter uint SECRET1_DIGEST_ADDR = Secret1DigestOffset / (TL_DW / 8);
  parameter uint SECRET1_END_ADDR    = SECRET1_DIGEST_ADDR - 1;

  parameter uint SECRET2_START_ADDR  = Secret2Offset / (TL_DW / 8);
  parameter uint SECRET2_DIGEST_ADDR = Secret2DigestOffset / (TL_DW / 8);
  parameter uint SECRET2_END_ADDR    = SECRET2_DIGEST_ADDR - 1;

  // TODO: did not count for LC partition
  parameter uint OTP_ARRAY_SIZE = (CreatorSwCfgSize + OwnerSwCfgSize + HwCfgSize + Secret0Size +
                                   Secret1Size + Secret2Size) / (TL_DW / 8);

  // Total num of valid dai address, secret partitions have a granularity of 8, the rest have
  // a granularity of 4. Subtract 8 for each digest.
  parameter uint DAI_ADDR_SIZE =
      (CreatorSwCfgSize + OwnerSwCfgSize + HwCfgSize - 3 * 8) / 4 +
      (Secret0Size + Secret1Size + Secret2Size - 3 * 8) / 8 ;

  // sram rsp data has 1 bit for seed_valid, the rest are for key and nonce
  parameter uint SRAM_DATA_SIZE = 1 + SramKeyWidth + SramNonceWidth;
  // otbn rsp data has 1 bit for seed_valid, the rest are for key and nonce
  parameter uint OTBN_DATA_SIZE = 1 + OtbnKeyWidth + OtbnNonceWidth;
  // flash rsp data has 1 bit for seed_valid, the rest are for key
  parameter uint FLASH_DATA_SIZE = 1 + FlashKeyWidth;
  // lc program data has lc_state data and lc_cnt data
  parameter uint LC_PROG_DATA_SIZE = LcStateWidth + LcCountWidth;

  // scramble related parameters
  parameter uint SCRAMBLE_DATA_SIZE = 64;
  parameter uint SCRAMBLE_KEY_SIZE  = 128;
  parameter uint NUM_ROUND          = 31;

  parameter uint NUM_SRAM_EDN_REQ = 10;
  parameter uint NUM_OTBN_EDN_REQ = 16;

  parameter uint CHK_TIMEOUT_CYC = 40;

  // lc does not have digest
  parameter int PART_BASE_ADDRS [NumPart-1] = {
    CreatorSwCfgOffset,
    OwnerSwCfgOffset,
    HwCfgOffset,
    Secret0Offset,
    Secret1Offset,
    Secret2Offset
  };

  // types
  typedef enum bit [1:0] {
    OtpOperationDone,
    OtpErr,
    NumOtpCtrlIntr
  } otp_intr_e;

  typedef enum bit [4:0] {
    OtpCreatorSwCfgErrIdx,
    OtpOwnerSwCfgErrIdx,
    OtpHwCfgErrIdx,
    OtpSecret0ErrIdx,
    OtpSecret1ErrIdx,
    OtpSecret2ErrIdx,
    OtpLifeCycleErrIdx,
    OtpDaiErrIdx,
    OtpLciErrIdx,
    OtpTimeoutErrIdx,
    OtpLfsrFsmErrIdx,
    OtpScramblingFsmErrIdx,
    OtpDerivKeyFsmErrIdx,
    OtpDaiIdleIdx,
    OtpCheckPendingIdx
  } otp_status_e;

  typedef enum bit [2:0] {
    OtpNoError,
    OtpMacroError,
    OtpMacroEccCorrError,
    OtpMacroEccUncorrError,
    OtpMacroWriteBlankError,
    OtpAccessError,
    OtpCheckFailError,
    OtpFsmStateError
  } otp_err_code_e;

  typedef enum bit [1:0] {
    OtpNoEccErr,
    OtpEccCorrErr,
    OtpEccUncorrErr
  } otp_ecc_err_e;

  typedef virtual mem_bkdr_if #(.MEM_ECC(1)) mem_bkdr_vif;
  typedef virtual otp_ctrl_if otp_ctrl_vif;

  // functions
  function automatic int get_part_index(bit [TL_DW-1:0] addr);
    int index;
    for (index = 0; index < NumPart; index++) begin
      if (PartInfo[index].offset > addr) begin
        index--;
        break;
      end
    end
    if (index == NumPart) index--;
    return index;
  endfunction

  function automatic bit is_secret(bit [TL_DW-1:0] addr);
    int part_index = get_part_index(addr);
    if (part_index inside {[Secret0Idx:Secret2Idx]}) return 1;
    else return 0;
  endfunction

  function automatic bit is_sw_digest(bit [TL_DW-1:0] addr);
    if ({addr[TL_DW-1:3], 3'b0} inside {CreatorSwCfgDigestOffset, OwnerSwCfgDigestOffset}) begin
      return 1;
    end else begin
      return 0;
    end
  endfunction

  function automatic bit is_digest(bit [TL_DW-1:0] addr);
    if (is_sw_digest(addr)) return 1;
    if ({addr[TL_DW-1:3], 3'b0} inside {HwCfgDigestOffset, Secret0DigestOffset,
                                        Secret1DigestOffset, Secret2DigestOffset}) begin
      return 1;
    end else begin
      return 0;
    end
  endfunction

  function automatic bit is_sw_part(bit [TL_DW-1:0] addr);
    int part_idx = get_part_index(addr);
    if (part_idx inside {CreatorSwCfgDigestOffset, OwnerSwCfgDigestOffset}) return 1;
    else return 0;
  endfunction

  // Resolve an offset within the software window as an offset within the whole otp_ctrl block.
  function automatic bit [TL_AW-1:0] get_sw_window_offset(bit [TL_AW-1:0] dai_addr);
    return dai_addr + SW_WINDOW_BASE_ADDR;
  endfunction

  // package sources
  `include "otp_ctrl_env_cfg.sv"
  `include "otp_ctrl_env_cov.sv"
  `include "otp_ctrl_virtual_sequencer.sv"
  `include "otp_ctrl_scoreboard.sv"
  `include "otp_ctrl_env.sv"
  `include "otp_ctrl_vseq_list.sv"

endpackage
