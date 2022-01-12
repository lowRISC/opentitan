// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class lc_ctrl_env_cov extends cip_base_env_cov #(
  .CFG_T(lc_ctrl_env_cfg)
);
  `uvm_component_utils(lc_ctrl_env_cov)

  // the base class provides the following handles for use:
  // lc_ctrl_env_cfg: cfg

  // covergroups

  // State error injections
  covergroup err_inj_cg;
    clk_byp_error_rsp_cp: coverpoint cfg.err_inj.clk_byp_error_rsp;
    flash_rma_error_rsp_cp: coverpoint cfg.err_inj.flash_rma_error_rsp;
    otp_prog_err_cp: coverpoint cfg.err_inj.otp_prog_err;
    token_mismatch_err_cp: coverpoint cfg.err_inj.token_mismatch_err;
    state_err_cp: coverpoint cfg.err_inj.state_err;
    state_backdoor_err_cp: coverpoint cfg.err_inj.state_backdoor_err;
    count_err_cp: coverpoint cfg.err_inj.count_err;
    count_backdoor_err_cp: coverpoint cfg.err_inj.count_backdoor_err;
    transition_err_cp: coverpoint cfg.err_inj.transition_err;
    post_trans_err_cp: coverpoint cfg.err_inj.post_trans_err;

    // Cross for attempted second transition with and without failure
    state_post_trans_xp: cross post_trans_err_cp, state_err_cp, state_backdoor_err_cp,
        count_err_cp, count_backdoor_err_cp;

  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    err_inj_cg = new();
  endfunction : new

  virtual function void sample_cov();
    err_inj_cg.sample();
  endfunction

endclass
