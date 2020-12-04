// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package otp_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import push_pull_agent_pkg::*;
  import otp_ctrl_ral_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_pkg::*;
  import otp_ctrl_part_pkg::*;
  import lc_ctrl_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[]      = {"otp_macro_failure", "otp_check_failure"};
  parameter uint NUM_ALERTS              = 2;

  parameter uint DIGEST_SIZE             = 8;
  parameter uint SW_WINDOW_BASE_ADDR     = 'h1000;
  parameter uint TEST_ACCESS_BASE_ADDR   = 'h2000;
  parameter uint SW_WINDOW_SIZE          = 512 * 4;
  parameter uint TEST_ACCESS_WINDOW_SIZE = 16 * 4;
  // convert byte into TLUL width size
  parameter uint HW_CFG_ARRAY_SIZE       = HwCfgContentSize / (TL_DW / 8);

  // sram rsp data has 1 bit for seed_valid, the rest are for key and nonce
  parameter uint SRAM_DATA_SIZE  = 1 + SramKeyWidth + SramNonceWidth;
  // otbn rsp data has 1 bit for seed_valid, the rest are for key and nonce
  parameter uint OTBN_DATA_SIZE  = 1 + OtbnKeyWidth + OtbnNonceWidth;
  // flash rsp data has 1 bit for seed_valid, the rest are for key
  parameter uint FLASH_DATA_SIZE = 1 + FlashKeyWidth;
  // edn rsp data are key width
  parameter uint EDN_DATA_SIZE   = EdnDataWidth;

  // scramble related parameters
  parameter uint SCRAMBLE_DATA_SIZE = 64;
  parameter uint SCRAMBLE_KEY_SIZE  = 128;
  parameter uint NUM_ROUND          = 31;

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

  typedef enum bit [14:0] {
    OtpCheckPending     = 15'b100_0000_0000_0000,
    OtpDaiIdle          = 15'b010_0000_0000_0000,
    OtpDerivKeyFsmErr   = 15'b001_0000_0000_0000,
    OtpScramblingFsmErr = 15'b000_1000_0000_0000,
    OtpLfsrFsmErr       = 15'b000_0100_0000_0000,
    OtpTimeoutErr       = 15'b000_0010_0000_0000,
    OtpLciErr           = 15'b000_0001_0000_0000,
    OtpDaiErr           = 15'b000_0000_1000_0000,
    OtpLifeCycleErr     = 15'b000_0000_0100_0000,
    OtpSecret2Err       = 15'b000_0000_0010_0000,
    OtpSecret1Err       = 15'b000_0000_0001_0000,
    OtpSecret0Err       = 15'b000_0000_0000_1000,
    OtpHwCfgErr         = 15'b000_0000_0000_0100,
    OtpOwnerSwCfgErr    = 15'b000_0000_0000_0010,
    OtpCreatorSwCfgErr  = 15'b000_0000_0000_0001
  } otp_status_e;

  typedef enum bit [1:0] {
    OtpPwrInitReq,
    OtpPwrIdleRsp,
    OtpPwrDoneRsp,
    OtpPwrIfWidth
  } otp_pwr_if_e;

  typedef virtual pins_if #(OtpPwrIfWidth) pwr_otp_vif;
  typedef virtual pins_if #(4)             lc_provision_en_vif;
  typedef virtual pins_if #(4)             lc_dft_en_vif;
  typedef virtual mem_bkdr_if              mem_bkdr_vif;
  typedef virtual otp_ctrl_output_data_if  otp_ctrl_output_data_vif;

  // functions
  function automatic int get_part_index(bit [TL_DW-1:0] addr);
    int index;
    for (index = 0; index < NumPart; index++) begin
      if (PartInfo[index].offset > addr) begin
        index--;
        break;
      end
    end
    return index;
  endfunction

  function automatic bit is_secret(bit [TL_DW-1:0] addr);
    int part_index = get_part_index(addr);
    if (part_index inside {[Secret0Idx:Secret2Idx]}) return 0;
    else return 1;
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
