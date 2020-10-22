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
  parameter uint DIGEST_SIZE             = 8;
  parameter uint SW_WINDOW_BASE_ADDR     = 'h1000;
  parameter uint TEST_ACCESS_BASE_ADDR   = 'h2000;
  parameter uint SW_WINDOW_SIZE          = 512 * 4;
  parameter uint TEST_ACCESS_WINDOW_SIZE = 16 * 4;

  // sram rsp data has 1 bit for seed_valid, the rest are for key and nonce
  parameter uint SRAM_DATA_SIZE  = 1 + SramKeyWidth + SramNonceWidth;
  // otbn rsp data has 1 bit for seed_valid, the rest are for key and nonce
  parameter uint OTBN_DATA_SIZE  = 1 + OtbnKeyWidth + OtbnNonceWidth;
  // flash rsp data has 1 bit for seed_valid, the rest are for key
  parameter uint FLASH_DATA_SIZE = 1 + FlashKeyWidth;

  // lc does not have digest
  parameter bit[10:0] DIGESTS_ADDR [NumPart-1] = {
      CreatorSwCfgDigestOffset,
      OwnerSwCfgDigestOffset,
      HwCfgDigestOffset,
      Secret0DigestOffset,
      Secret1DigestOffset,
      Secret2DigestOffset
  };

  // types
  typedef virtual pins_if #(3) pwr_otp_vif;
  typedef virtual pins_if #(4) lc_provision_en_vif;
  typedef virtual pins_if #(4) lc_dft_en_vif;
  typedef virtual mem_bkdr_if mem_bkdr_vif;

  typedef enum bit [1:0] {
    OtpOperationDone,
    OtpErr,
    NumOtpCtrlIntr
  } otp_intr_e;

  // TODO: needs update once design finalize
  typedef enum bit [6:0] {
    OtpCheckPending = 7'b0_000_001,
    OtpIdle         = 7'b0_000_010,
    OtpKeyFsmErr    = 7'b0_000_100,
    OtpScrmblFsmErr = 7'b0_001_000,
    OtpLfsrFsmErr   = 7'b0_010_000,
    OtpChkTimeout   = 7'b0_100_000,
    OptPartErrs     = 7'b1_000_000
  } otp_status_e;

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

  function automatic bit [TL_AW-1:0] get_sw_window_addr(bit [TL_AW-1:0] dai_addr);
    get_sw_window_addr = dai_addr + SW_WINDOW_BASE_ADDR;
  endfunction

  // package sources
  `include "otp_ctrl_env_cfg.sv"
  `include "otp_ctrl_env_cov.sv"
  `include "otp_ctrl_virtual_sequencer.sv"
  `include "otp_ctrl_scoreboard.sv"
  `include "otp_ctrl_env.sv"
  `include "otp_ctrl_vseq_list.sv"

endpackage
