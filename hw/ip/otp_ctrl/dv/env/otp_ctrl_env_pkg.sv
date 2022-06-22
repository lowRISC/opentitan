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
  import otp_ctrl_core_ral_pkg::*;
  import otp_ctrl_prim_ral_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_pkg::*;
  import otp_ctrl_part_pkg::*;
  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
  import lc_ctrl_dv_utils_pkg::*;
  import mem_bkdr_util_pkg::*;
  import otp_scrambler_pkg::*;
  import sec_cm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[]      = {"fatal_macro_error",
                                            "fatal_check_error",
                                            "fatal_bus_integ_error"};
  parameter uint NUM_ALERTS              = 3;
  parameter uint NUM_EDN                 = 1;

  parameter uint DIGEST_SIZE             = 8;
  parameter uint SW_WINDOW_BASE_ADDR     = 'h1000;
  parameter uint SW_WINDOW_SIZE          = 512 * 4;

  // convert byte into TLUL width size
  parameter uint VENDOR_TEST_START_ADDR  = VendorTestOffset / (TL_DW / 8);
  parameter uint VENDOR_TEST_DIGEST_ADDR = VendorTestDigestOffset / (TL_DW / 8);
  parameter uint VENDOR_TEST_END_ADDR    = VENDOR_TEST_DIGEST_ADDR - 1;

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

  // LC has its own storage in scb
  parameter uint OTP_ARRAY_SIZE = (VendorTestSize + CreatorSwCfgSize + OwnerSwCfgSize +
                                   HwCfgSize + Secret0Size + Secret1Size + Secret2Size)
                                   / (TL_DW / 8);

  parameter int OTP_ADDR_WIDTH = 11;

  parameter uint NUM_PRIM_REG = 8;

  // Total num of valid dai address, secret partitions have a granularity of 8, the rest have
  // a granularity of 4. Subtract 8 for each digest.
  parameter uint DAI_ADDR_SIZE =
      (VendorTestSize + CreatorSwCfgSize + OwnerSwCfgSize + HwCfgSize - 4 * 8) / 4 +
      (Secret0Size + Secret1Size + Secret2Size - 3 * 8) / 8 ;

  // sram rsp data has 1 bit for seed_valid, the rest are for key and nonce
  parameter uint SRAM_DATA_SIZE = 1 + SramKeyWidth + SramNonceWidth;
  // otbn rsp data has 1 bit for seed_valid, the rest are for key and nonce
  parameter uint OTBN_DATA_SIZE = 1 + OtbnKeyWidth + OtbnNonceWidth;
  // flash rsp data has 1 bit for seed_valid, the rest are for key
  parameter uint FLASH_DATA_SIZE = 1 + FlashKeyWidth;
  // lc program data has lc_state data and lc_cnt data
  parameter uint LC_PROG_DATA_SIZE = LcStateWidth + LcCountWidth;

  parameter uint NUM_SRAM_EDN_REQ = 12;
  parameter uint NUM_OTBN_EDN_REQ = 10;

  parameter uint NUM_UNBUFF_PARTS = 3;
  parameter uint NUM_BUFF_PARTS   = 5;

  parameter uint CHK_TIMEOUT_CYC = 40;

  // When fatal alert triggered, all partitions go to error state and status will be
  // set to 1.
  parameter bit [9:0] FATAL_EXP_STATUS = '1;

  // lc does not have dai access
  parameter int PART_BASE_ADDRS [NumPart-1] = {
    VendorTestOffset,
    CreatorSwCfgOffset,
    OwnerSwCfgOffset,
    HwCfgOffset,
    Secret0Offset,
    Secret1Offset,
    Secret2Offset
  };

  // lc does not have digest
  parameter int PART_OTP_DIGEST_ADDRS [NumPart-1] = {
    VendorTestDigestOffset   >> 2,
    CreatorSwCfgDigestOffset >> 2,
    OwnerSwCfgDigestOffset   >> 2,
    HwCfgDigestOffset        >> 2,
    Secret0DigestOffset      >> 2,
    Secret1DigestOffset      >> 2,
    Secret2DigestOffset      >> 2
  };

  // types
  typedef enum bit [1:0] {
    OtpOperationDone,
    OtpErr,
    NumOtpCtrlIntr
  } otp_intr_e;

  typedef enum bit [5:0] {
    OtpVendorTestErrIdx,
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
    OtpBusIntegErrorIdx,
    OtpDaiIdleIdx,
    OtpCheckPendingIdx,
    OtpStatusFieldSize
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

  typedef enum bit [1:0] {
    OtpNoAlert,
    OtpCheckAlert,
    OtpMacroAlert
  } otp_alert_e;

  typedef struct packed {
    bit read_lock;
    bit write_lock;
  } otp_part_access_lock_t;

  // OTP conditions when driving specific port.
  typedef enum bit [2:0] {
    DuringOTPInit,
    DuringOTPDaiBusy,
    DuringOTPDaiDigest,
    DuringOTPRead,
    DriveRandomly
  } port_drive_condition_e;

  typedef virtual otp_ctrl_if otp_ctrl_vif;

  parameter otp_err_code_e OTP_TERMINAL_ERRS[4] = {OtpMacroEccUncorrError,
                                                   OtpCheckFailError,
                                                   OtpFsmStateError,
                                                   OtpMacroError};

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
    if ({addr[TL_DW-1:3], 3'b0} inside {VendorTestDigestOffset,
                                        CreatorSwCfgDigestOffset,
                                        OwnerSwCfgDigestOffset}) begin
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
    return is_sw_part_idx(part_idx);
  endfunction

  function automatic bit is_sw_part_idx(int part_idx);
    if (part_idx inside {VendorTestIdx, CreatorSwCfgIdx, OwnerSwCfgIdx}) return 1;
    else return 0;
  endfunction

  // Returns true if this partition only has ECC correctable error.
  // If the partition has ECC uncorrectable error, design will still categorize it as ECC
  // correctable error.
  function automatic bit ecc_corr_err_only_part(int part_idx);
    return part_idx == VendorTestIdx;
  endfunction

  // Resolve an offset within the software window as an offset within the whole otp_ctrl block.
  function automatic bit [TL_AW-1:0] get_sw_window_offset(bit [TL_AW-1:0] dai_addr);
    return dai_addr + SW_WINDOW_BASE_ADDR;
  endfunction

  function automatic bit [TL_DW-1:0] normalize_dai_addr(bit [TL_DW-1:0] dai_addr);
    normalize_dai_addr = (is_secret(dai_addr) || is_digest(dai_addr)) ? dai_addr >> 3 << 3 :
                                                                        dai_addr >> 2 << 2;
  endfunction

  // package sources
  `include "otp_ctrl_ast_inputs_cfg.sv"
  `include "otp_ctrl_env_cfg.sv"
  `include "otp_ctrl_env_cov.sv"
  `include "otp_ctrl_virtual_sequencer.sv"
  `include "otp_ctrl_scoreboard.sv"
  `include "otp_ctrl_env.sv"
  `include "otp_ctrl_vseq_list.sv"

endpackage
