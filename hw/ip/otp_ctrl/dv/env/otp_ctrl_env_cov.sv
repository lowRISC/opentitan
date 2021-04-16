// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class otp_ctrl_env_cov extends cip_base_env_cov #(
  .CFG_T(otp_ctrl_env_cfg)
);
  `uvm_component_utils(otp_ctrl_env_cov)

  // the base class provides the following handles for use:
  // otp_ctrl_env_cfg: cfg

  // covergroups
  // This covergroup collects different conditions when outputs (hwcfg_o, keymgr_key_o) are checked
  // in scb:
  // - If lc_esc_en is On
  // - If each partition is locked (expect LC)
  covergroup power_on_cg with function sample (bit lc_esc_en, bit [NumPart-2:0] parts_locked);
    lc_esc: coverpoint lc_esc_en;
    creator_sw_lock: coverpoint parts_locked[0];
    owner_sw_lock: coverpoint parts_locked[1];
    hw_cfg_lock: coverpoint parts_locked[2];
    screct0_lock: coverpoint parts_locked[3];
    screct1_lock: coverpoint parts_locked[4];
    screct2_lock: coverpoint parts_locked[5];
  endgroup

  bit_toggle_cg_wrap lc_prog_cg;
  bit_toggle_cg_wrap otbn_req_cg;

  // This coverpoint is only collected if flash request passed scb check
  covergroup flash_req_cg with function sample (int index, bit locked);
    flash_index: coverpoint index {
      bins flash_data_key = {FlashDataKey};
      bins flash_addr_key = {FlashAddrKey};
      illegal_bins il = default;
    }
    secret1_lock: coverpoint locked;
    flash_req_lock_cross: cross flash_index, secret1_lock;
  endgroup

  // This coverpoint is only collected if sram request passed scb check
  covergroup sram_req_cg with function sample (int index, bit locked);
    sram_index: coverpoint index {
      bins sram_key0 = {0};
      bins sram_key1 = {1};
      illegal_bins il = default;
    }
    secret1_lock: coverpoint locked;
    sram_req_lock_cross: cross sram_index, secret1_lock;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    power_on_cg  = new();
    flash_req_cg = new();
    sram_req_cg  = new();
    lc_prog_cg   = new("lc_prog_cg", "", 0);
    otbn_req_cg  = new("otbn_req_cg", "", 0);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // [or instantiate covergroups here]
    // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
    // See cip_base_env_cov for details
  endfunction

endclass
