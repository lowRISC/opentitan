// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

// Wrapper class for peripheral clock covergroup.
class clkmgr_peri_cg_wrap;
  // This covergroup collects signals affecting peripheral clock.
  covergroup peri_cg(string name) with function sample(bit enable, bit ip_clk_en, bit scanmode);
    option.name = name;

    csr_enable_cp: coverpoint enable;
    ip_clk_en_cp: coverpoint ip_clk_en;
    scanmode_cp: coverpoint scanmode;
  endgroup

  function new(string name);
    peri_cg = new(name);
  endfunction

  function void sample(bit enable, bit ip_clk_en, bit scanmode);
    peri_cg.sample(enable, ip_clk_en, scanmode);
  endfunction
endclass

// Wrapper class for transactional unit clock covergroup.
class clkmgr_trans_cg_wrap;
  // This covergroup collects signals affecting transactional clock.
  covergroup trans_cg(string name) with function
      sample(bit hint, bit ip_clk_en, bit scanmode, bit idle);
    option.name = name;

    csr_hint_cp: coverpoint hint;
    ip_clk_en_cp: coverpoint ip_clk_en;
    scanmode_cp: coverpoint scanmode;
    idle_cp: coverpoint idle;
  endgroup

  function new(string name);
    trans_cg = new(name);
  endfunction

  function sample(bit hint, bit ip_clk_en, bit scanmode, bit idle);
    trans_cg.sample(hint, ip_clk_en, scanmode, idle);
  endfunction
endclass

class clkmgr_env_cov extends cip_base_env_cov #(.CFG_T(clkmgr_env_cfg));
  import clkmgr_env_pkg::*;

  `uvm_component_utils(clkmgr_env_cov)

  // the base class provides the following handles for use:
  // clkmgr_env_cfg: cfg

  // covergroups

  // These covergroups collect signals affecting peripheral clocks.
  clkmgr_peri_cg_wrap io_div4_peri_cg_wrap;
  clkmgr_peri_cg_wrap io_div2_peri_cg_wrap;
  clkmgr_peri_cg_wrap usb_peri_cg_wrap;

  // These covergroups collect signals affecting transactional clocks.
  clkmgr_trans_cg_wrap aes_trans_cg_wrap;
  clkmgr_trans_cg_wrap hmac_trans_cg_wrap;
  clkmgr_trans_cg_wrap kmac_trans_cg_wrap;
  clkmgr_trans_cg_wrap otbn_trans_cg_wrap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // The peripheral covergoups.
    io_div4_peri_cg_wrap = new("io_div4_peri");
    io_div2_peri_cg_wrap = new("io_div2_peri");
    usb_peri_cg_wrap = new("usb_peri");

    // The transactional covergroups.
    aes_trans_cg_wrap = new("aes");
    hmac_trans_cg_wrap = new("hmac");
    kmac_trans_cg_wrap = new("kmac");
    otbn_trans_cg_wrap = new("otbn");
  endfunction : new

  function void update_peri_cgs(logic [NUM_PERI-1:0] enables, logic ip_clk_en, logic scanmode);
    io_div4_peri_cg_wrap.sample(enables[int'(PeriDiv4)], ip_clk_en, scanmode);
    io_div2_peri_cg_wrap.sample(enables[int'(PeriDiv2)], ip_clk_en, scanmode);
    usb_peri_cg_wrap.sample(enables[int'(PeriUsb)], ip_clk_en, scanmode);
  endfunction

  function void update_trans_cgs(logic [NUM_TRANS-1:0] hints, logic ip_clk_en, logic scanmode,
                                 logic [NUM_TRANS-1:0] idle);
    aes_trans_cg_wrap.sample(hints[int'(TransAes)], ip_clk_en, scanmode, idle[int'(TransAes)]);
    hmac_trans_cg_wrap.sample(hints[int'(TransHmac)], ip_clk_en, scanmode, idle[int'(TransHmac)]);
    kmac_trans_cg_wrap.sample(hints[int'(TransKmac)], ip_clk_en, scanmode, idle[int'(TransKmac)]);
    otbn_trans_cg_wrap.sample(hints[int'(TransOtbn)], ip_clk_en, scanmode, idle[int'(TransOtbn)]);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // [or instantiate covergroups here]
    // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
    // See cip_base_env_cov for details
  endfunction

endclass
