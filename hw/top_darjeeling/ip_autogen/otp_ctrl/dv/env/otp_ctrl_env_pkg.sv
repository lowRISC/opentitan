// Copyright lowRISC contributors (OpenTitan project).
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
  import otp_macro_prim_ral_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_pkg::*;
  import otp_ctrl_part_pkg::*;
  import otp_ctrl_top_specific_pkg::*;
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
  parameter uint NUM_ALERTS = 5;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {"fatal_macro_error",
                                                 "fatal_check_error",
                                                 "fatal_bus_integ_error",
                                                 "fatal_prim_otp_alert",
                                                 "recov_prim_otp_alert"};
  parameter uint NUM_EDN             = 1;

  parameter uint DIGEST_SIZE         = 8;
  parameter uint SW_WINDOW_BASE_ADDR = 'h8000;
  parameter uint SW_WINDOW_SIZE      = NumSwCfgWindowWords * 4;

  parameter uint TL_SIZE = (TL_DW / 8);
  // LC has its own storage in scb
  // we can use the LC offset here because it will always be the last partition.
  parameter uint OTP_ARRAY_SIZE = LcTransitionCntOffset / TL_SIZE;

  parameter int OTP_ADDR_WIDTH = OtpByteAddrWidth-2;

  parameter uint NUM_PRIM_REG = 8;

  // sram rsp data has 1 bit for seed_valid, the rest are for key and nonce
  parameter uint SRAM_DATA_SIZE = 1 + SramKeyWidth + SramNonceWidth;
  // otbn rsp data has 1 bit for seed_valid, the rest are for key and nonce
  parameter uint OTBN_DATA_SIZE = 1 + OtbnKeyWidth + OtbnNonceWidth;
  // lc program data has lc_state data and lc_cnt data
  parameter uint LC_PROG_DATA_SIZE = LcStateWidth + LcCountWidth;

  parameter uint NUM_SRAM_EDN_REQ = 12;
  parameter uint NUM_OTBN_EDN_REQ = 10;

  // This is used to randomize CHECK_TIMEOUT in sequences, set to a low value
  // so it will certainly cause a check error due to a timeout.
  parameter uint CHK_TIMEOUT_CYC = 40;
  // This is some slack for a timeout error propagation to become an alert.
  parameter uint CHK_TIMEOUT_SLACK = 4;

  // When fatal alert triggered, all partitions and the DAI & LCI go to error state and status will
  // be set to 1.
  parameter bit [NumErrorEntries-1:0] FATAL_EXP_STATUS = '1;

  // lc does not have dai access
  parameter int PART_BASE_ADDRS [NumPart-1] = {
    VendorTestOffset,
    CreatorSwCfgOffset,
    OwnerSwCfgOffset,
    OwnershipSlotStateOffset,
    RotCreatorIdentityOffset,
    RotOwnerAuthSlot0Offset,
    RotOwnerAuthSlot1Offset,
    PlatIntegAuthSlot0Offset,
    PlatIntegAuthSlot1Offset,
    PlatOwnerAuthSlot0Offset,
    PlatOwnerAuthSlot1Offset,
    PlatOwnerAuthSlot2Offset,
    PlatOwnerAuthSlot3Offset,
    ExtNvmOffset,
    RomPatchOffset,
    SocFusesCpOffset,
    SocFusesFtOffset,
    ScratchFusesOffset,
    HwCfg0Offset,
    HwCfg1Offset,
    HwCfg2Offset,
    Secret0Offset,
    Secret1Offset,
    Secret2Offset,
    Secret3Offset
  };

  // lc does not have digest
  parameter int PART_OTP_DIGEST_ADDRS [NumPart-1] = {
    VendorTestDigestOffset >> 2,
    CreatorSwCfgDigestOffset >> 2,
    OwnerSwCfgDigestOffset >> 2,
    -1, // This partition does not have a digest.
    RotCreatorIdentityDigestOffset >> 2,
    RotOwnerAuthSlot0DigestOffset >> 2,
    RotOwnerAuthSlot1DigestOffset >> 2,
    PlatIntegAuthSlot0DigestOffset >> 2,
    PlatIntegAuthSlot1DigestOffset >> 2,
    PlatOwnerAuthSlot0DigestOffset >> 2,
    PlatOwnerAuthSlot1DigestOffset >> 2,
    PlatOwnerAuthSlot2DigestOffset >> 2,
    PlatOwnerAuthSlot3DigestOffset >> 2,
    -1, // This partition does not have a digest.
    RomPatchDigestOffset >> 2,
    SocFusesCpDigestOffset >> 2,
    SocFusesFtDigestOffset >> 2,
    -1, // This partition does not have a digest.
    HwCfg0DigestOffset >> 2,
    HwCfg1DigestOffset >> 2,
    HwCfg2DigestOffset >> 2,
    Secret0DigestOffset >> 2,
    Secret1DigestOffset >> 2,
    Secret2DigestOffset >> 2,
    Secret3DigestOffset >> 2
  };

  parameter int PART_OTP_ZEROIZED_ADDRS [NumPart-1] = {
    VendorTestZerOffset >> 2,
    CreatorSwCfgZerOffset >> 2,
    OwnerSwCfgZerOffset >> 2,
    OwnershipSlotStateZerOffset >> 2,
    RotCreatorIdentityZerOffset >> 2,
    RotOwnerAuthSlot0ZerOffset >> 2,
    RotOwnerAuthSlot1ZerOffset >> 2,
    PlatIntegAuthSlot0ZerOffset >> 2,
    PlatIntegAuthSlot1ZerOffset >> 2,
    PlatOwnerAuthSlot0ZerOffset >> 2,
    PlatOwnerAuthSlot1ZerOffset >> 2,
    PlatOwnerAuthSlot2ZerOffset >> 2,
    PlatOwnerAuthSlot3ZerOffset >> 2,
    ExtNvmZerOffset >> 2,
    RomPatchZerOffset >> 2,
    -1, // This partition has no zeroized field.
    -1, // This partition has no zeroized field.
    ScratchFusesZerOffset >> 2,
    HwCfg0ZerOffset >> 2,
    HwCfg1ZerOffset >> 2,
    HwCfg2ZerOffset >> 2,
    Secret0ZerOffset >> 2,
    Secret1ZerOffset >> 2,
    Secret2ZerOffset >> 2,
    Secret3ZerOffset >> 2
  };

  // types
  typedef enum bit [1:0] {
    OtpOperationDone,
    OtpErr,
    NumOtpCtrlIntr
  } otp_intr_e;

  typedef enum bit [3:0] {
    OtpPartitionErrorIdx,
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

  typedef enum int {
    OtpPartitionVendorTestIdx,
    OtpPartitionCreatorSwCfgIdx,
    OtpPartitionOwnerSwCfgIdx,
    OtpPartitionOwnershipSlotStateIdx,
    OtpPartitionRotCreatorIdentityIdx,
    OtpPartitionRotOwnerAuthSlot0Idx,
    OtpPartitionRotOwnerAuthSlot1Idx,
    OtpPartitionPlatIntegAuthSlot0Idx,
    OtpPartitionPlatIntegAuthSlot1Idx,
    OtpPartitionPlatOwnerAuthSlot0Idx,
    OtpPartitionPlatOwnerAuthSlot1Idx,
    OtpPartitionPlatOwnerAuthSlot2Idx,
    OtpPartitionPlatOwnerAuthSlot3Idx,
    OtpPartitionExtNvmIdx,
    OtpPartitionRomPatchIdx,
    OtpPartitionSocFusesCpIdx,
    OtpPartitionSocFusesFtIdx,
    OtpPartitionScratchFusesIdx,
    OtpPartitionHwCfg0Idx,
    OtpPartitionHwCfg1Idx,
    OtpPartitionHwCfg2Idx,
    OtpPartitionSecret0Idx,
    OtpPartitionSecret1Idx,
    OtpPartitionSecret2Idx,
    OtpPartitionSecret3Idx,
    OtpPartitionLifeCycleIdx
  } otp_partition_e;


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
    return PartInfo[part_index].secret;
  endfunction

  function automatic bit part_has_digest(int part_idx);
    return PartInfo[part_idx].hw_digest || PartInfo[part_idx].sw_digest;
  endfunction

  function automatic bit part_has_hw_digest(int part_idx);
    return PartInfo[part_idx].hw_digest;
  endfunction

  // Return the address of the last 64 bits of the given partition
  function automatic bit [TL_DW-1:0] last_64_addr(int unsigned part_idx);
    return (PartInfo[part_idx].offset + PartInfo[part_idx].size) - 8;
  endfunction

  // Return true if the address points into the first 32 bits of a partition digest for the given
  // partition (HW or SW)
  function automatic bit is_digest_for(bit [TL_DW-1:0] addr, int unsigned part_idx);
    if (!PartInfo[part_idx].sw_digest && !PartInfo[part_idx].hw_digest) return 0;

    // If the partition contains a digest, it will be the last 64 bits of the partition, unless
    // there is also a zeroization marker. When both are present, the digest comes just before the
    // zeroisation marker.
    return {addr[TL_DW-1:3], 3'b0} == (last_64_addr(part_idx) -
                                       (PartInfo[part_idx].zeroizable ? 8 : 0));
  endfunction

  function automatic bit is_sw_digest(bit [TL_DW-1:0] addr);
    int part_idx = get_part_index(addr);
    return PartInfo[part_idx].sw_digest && is_digest_for(addr, part_idx);
  endfunction

  function automatic bit is_digest(bit [TL_DW-1:0] addr);
    return is_digest_for(addr, get_part_index(addr));
  endfunction

  // Return true if this is the address of the Zeroize marker for a partition with zeroization
  function automatic bit is_zeroize_marker(bit [TL_DW-1:0] addr);
    int unsigned part_idx = get_part_index(addr);

    // If the partition is zeroizable, its Zeroize status is in the last 64 bits of the partition.
    return (PartInfo[part_idx].zeroizable && (addr == last_64_addr(part_idx)));
  endfunction

  function automatic bit is_sw_part(bit [TL_DW-1:0] addr);
    int part_idx = get_part_index(addr);
    return is_sw_part_idx(part_idx);
  endfunction

  function automatic bit is_sw_part_idx(int part_idx);
    return (PartInfo[part_idx].variant == Unbuffered);
  endfunction

  function automatic bit is_hw_part(bit [TL_DW-1:0] addr);
    int part_idx = get_part_index(addr);
    return is_hw_part_idx(part_idx);
  endfunction

  function automatic bit is_hw_part_idx(int part_idx);
    return (PartInfo[part_idx].variant == Buffered);
  endfunction

  // Returns true if this partition supports ECC. Otherwise, no ECC errors are reported, and
  // the single bit errors are not corrected.
  function automatic bit part_has_integrity(int part_idx);
    return PartInfo[part_idx].integrity;
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
