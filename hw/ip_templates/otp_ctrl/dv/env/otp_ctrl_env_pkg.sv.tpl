// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gen_comment}
<%
from topgen.lib import Name

parts_without_lc = [part for part in otp_mmap.config["partitions"] if
                    part["variant"] in ["Buffered", "Unbuffered"]]
otp_size_as_hex_text =  f'{(2 ** otp_mmap.config["otp"]["byte_addr_width"]):x}'
%>\
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
  parameter string LIST_OF_ALERTS[] = {"fatal_macro_error",
                                       "fatal_check_error",
                                       "fatal_bus_integ_error",
                                       "fatal_prim_otp_alert",
                                       "recov_prim_otp_alert"};
  parameter uint NUM_ALERTS              = 5;
  parameter uint NUM_EDN                 = 1;

  parameter uint DIGEST_SIZE             = 8;
  parameter uint SW_WINDOW_BASE_ADDR     = 'h${otp_size_as_hex_text};
  parameter uint SW_WINDOW_SIZE          = NumSwCfgWindowWords * 4;

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
  // flash rsp data has 1 bit for seed_valid, the rest are for key
  parameter uint FLASH_DATA_SIZE = 1 + FlashKeyWidth;
  // lc program data has lc_state data and lc_cnt data
  parameter uint LC_PROG_DATA_SIZE = LcStateWidth + LcCountWidth;

  parameter uint NUM_SRAM_EDN_REQ = 12;
  parameter uint NUM_OTBN_EDN_REQ = 10;

  parameter uint CHK_TIMEOUT_CYC = 40;

  // When fatal alert triggered, all partitions and the DAI & LCI go to error state and status will
  // be set to 1.
  parameter bit [NumErrorEntries-1:0] FATAL_EXP_STATUS = '1;

  // lc does not have dai access
  parameter int PART_BASE_ADDRS [NumPart-1] = {
% for part in parts_without_lc:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
%>\
    ${part_name_camel}Offset${"" if loop.last else ","}
% endfor
  };

  // lc does not have digest
  parameter int PART_OTP_DIGEST_ADDRS [NumPart-1] = {
% for part in parts_without_lc:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
%>\
% if part["sw_digest"] or part["hw_digest"]:
    ${part_name_camel}DigestOffset >> 2${"" if loop.last else ","}
% else:
    -1${"" if loop.last else ","} // This partition does not have a digest.
% endif
% endfor
  };

  // types
  typedef enum bit [1:0] {
    OtpOperationDone,
    OtpErr,
    NumOtpCtrlIntr
  } otp_intr_e;

  typedef enum bit [5:0] {
% for part in otp_mmap.config["partitions"]:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
%>\
    Otp${part_name_camel}ErrIdx,
% endfor
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
    return PartInfo[part_index].secret;
  endfunction

  function automatic bit part_has_digest(int part_idx);
    return PartInfo[part_idx].hw_digest || PartInfo[part_idx].sw_digest;
  endfunction

  function automatic bit part_has_hw_digest(int part_idx);
    return PartInfo[part_idx].hw_digest;
  endfunction

  function automatic bit is_sw_digest(bit [TL_DW-1:0] addr);
    int part_idx = get_part_index(addr);
    if (PartInfo[part_idx].sw_digest) begin
      // If the partition contains a digest, it will be located in the last 64bit of the partition.
      return {addr[TL_DW-1:3], 3'b0} == ((PartInfo[part_idx].offset + PartInfo[part_idx].size) - 8);
    end else begin
      return 0;
    end
  endfunction

  function automatic bit is_digest(bit [TL_DW-1:0] addr);
    int part_idx = get_part_index(addr);
    if (PartInfo[part_idx].sw_digest || PartInfo[part_idx].hw_digest) begin
      // If the partition contains a digest, it will be located in the last 64bit of the partition.
      return {addr[TL_DW-1:3], 3'b0} == ((PartInfo[part_idx].offset + PartInfo[part_idx].size) - 8);
    end else begin
      return 0;
    end
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
