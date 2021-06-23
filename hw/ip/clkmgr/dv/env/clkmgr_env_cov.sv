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
    option.per_instance = 1;

    csr_enable_cp: coverpoint enable;
    ip_clk_en_cp: coverpoint ip_clk_en;
    scanmode_cp: coverpoint scanmode;

    peri_cross: cross csr_enable_cp, ip_clk_en_cp, scanmode_cp;
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
    option.per_instance = 1;

    csr_hint_cp: coverpoint hint;
    ip_clk_en_cp: coverpoint ip_clk_en;
    scanmode_cp: coverpoint scanmode;
    idle_cp: coverpoint idle;

    trans_cross: cross csr_hint_cp, ip_clk_en_cp, scanmode_cp, idle_cp;
  endgroup

  function new(string name);
    trans_cg = new(name);
  endfunction

  function void sample(bit hint, bit ip_clk_en, bit scanmode, bit idle);
    trans_cg.sample(hint, ip_clk_en, scanmode, idle);
  endfunction
endclass

class clkmgr_env_cov extends cip_base_env_cov #(.CFG_T(clkmgr_env_cfg));
  `uvm_component_utils(clkmgr_env_cov)

  // the base class provides the following handles for use:
  // clkmgr_env_cfg: cfg

  // These covergroups collect signals affecting peripheral clocks.
  clkmgr_peri_cg_wrap peri_cg_wrap[clkmgr_env_pkg::NUM_PERI];

  // These covergroups collect signals affecting transactional clocks.
  clkmgr_trans_cg_wrap trans_cg_wrap[clkmgr_env_pkg::NUM_TRANS];

  // This embeded covergroup collects coverage for the external clock functionality.
  covergroup extclk_cg with function
      sample(bit sel, bit dft_en, bit byp_req, bit scanmode);
    sel_cp: coverpoint sel;
    dft_en_cp: coverpoint dft_en;
    byp_req_cp: coverpoint byp_req;
    scanmode_cp: coverpoint scanmode;

    extclk_cross: cross sel_cp, dft_en_cp, byp_req_cp, scanmode_cp;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // The peripheral covergoups.
    foreach (peri_cg_wrap[i]) begin
      clkmgr_env_pkg::peri_e peri = clkmgr_env_pkg::peri_e'(i);
      peri_cg_wrap[i] = new(peri.name);
    end
    // The transactional covergroups.
    foreach (trans_cg_wrap[i]) begin
      clkmgr_env_pkg::trans_e trans = clkmgr_env_pkg::trans_e'(i);
      trans_cg_wrap[i] = new(trans.name);
    end
    extclk_cg = new();
  endfunction : new

  function void update_peri_cgs(logic [clkmgr_env_pkg::NUM_PERI-1:0] enables, logic ip_clk_en,
                                logic scanmode);
    foreach (peri_cg_wrap[i]) peri_cg_wrap[i].sample(enables[i], ip_clk_en, scanmode);
  endfunction

  function void update_trans_cgs(logic [clkmgr_env_pkg::NUM_TRANS-1:0] hints, logic ip_clk_en,
                                 logic scanmode, logic [clkmgr_env_pkg::NUM_TRANS-1:0] idle);
    foreach (trans_cg_wrap[i]) trans_cg_wrap[i].sample(hints[i], ip_clk_en, scanmode, idle[i]);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // [or instantiate covergroups here]
    // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
    // See cip_base_env_cov for details
  endfunction

endclass
