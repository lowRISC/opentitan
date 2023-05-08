// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

// verilog_format: off
// Cross a particular error condition with JTAG CSR
`ifndef LC_CTRL_JTAG_ERROR_CROSS
`define LC_CTRL_JTAG_ERROR_CROSS(error) \
  jtag_``error``_xp : cross jtag_csr_cp, error``_cp;
`endif

// Cross a particular error condition with post_trans_err
`ifndef LC_CTRL_POST_TRANS_CROSS
`define LC_CTRL_POST_TRANS_CROSS(error) \
  post_trans_``error``_xp : cross post_trans_err_cp, error``_cp;
`endif


class lc_ctrl_env_cov extends cip_base_env_cov #(
  .CFG_T(lc_ctrl_env_cfg)
);
  `uvm_component_utils(lc_ctrl_env_cov)

  // the base class provides the following handles for use:
  // lc_ctrl_env_cfg: cfg

  // Select error injections to mask for err_inj_cp
  const lc_ctrl_err_inj_t ErrInjMask = '{post_trans_err: 1, default:0};

  // covergroups

  // Volatile raw unlock coverpoint
  covergroup volatile_raw_unlock_cg with function sample(bit success);
    volatile_raw_unlock_cp: coverpoint success {
      bins success = {1};
      bins fail    = {0};
    }
  endgroup : volatile_raw_unlock_cg

  // Error injections
  covergroup err_inj_cg;

    // Any error injection
    // Ignore post_trans_err as this doesn't inject an error
    // it just tries a second transition


    err_inj_cp : coverpoint (cfg.err_inj & ~ErrInjMask) {
      bins no_err_inj = {0};
      bins err_inj    = {[1 : $]};
    }

    clk_byp_error_rsp_cp: coverpoint cfg.err_inj.clk_byp_error_rsp;
    flash_rma_error_rsp_cp: coverpoint cfg.err_inj.flash_rma_error_rsp;
    otp_prog_err_cp: coverpoint cfg.err_inj.otp_prog_err;
    otp_partition_err_cp: coverpoint cfg.err_inj.otp_partition_err;
    token_mismatch_err_cp: coverpoint cfg.err_inj.token_mismatch_err;
    token_invalid_err_cp:  coverpoint cfg.err_inj.token_invalid_err;
    token_response_err_cp:  coverpoint cfg.err_inj.token_response_err;
    otp_lc_data_i_valid_err_cp: coverpoint cfg.err_inj.otp_lc_data_i_valid_err;
    state_err_cp: coverpoint cfg.err_inj.state_err;
    state_illegal_err_cp: coverpoint cfg.err_inj.state_illegal_err;
    state_backdoor_err_cp: coverpoint cfg.err_inj.state_backdoor_err;
    lc_fsm_backdoor_err_cp: coverpoint cfg.err_inj.lc_fsm_backdoor_err;
    kmac_fsm_backdoor_err_cp: coverpoint cfg.err_inj.kmac_fsm_backdoor_err;
    count_err_cp: coverpoint cfg.err_inj.count_err;
    count_illegal_err_cp: coverpoint cfg.err_inj.count_illegal_err;
    count_backdoor_err_cp: coverpoint cfg.err_inj.count_backdoor_err;
    transition_err_cp: coverpoint cfg.err_inj.transition_err;
    transition_count_err_cp: coverpoint cfg.err_inj.transition_count_err;
    post_trans_err_cp: coverpoint cfg.err_inj.post_trans_err;
    security_escalation_err_cp: coverpoint cfg.err_inj.security_escalation_err;
    clk_byp_rsp_mubi_err_cp: coverpoint cfg.err_inj.clk_byp_rsp_mubi_err;
    flash_rma_rsp_mubi_err_cp: coverpoint cfg.err_inj.flash_rma_rsp_mubi_err;
    otp_secrets_valid_mubi_err_cp: coverpoint cfg.err_inj.otp_secrets_valid_mubi_err;
    otp_test_tokens_valid_mubi_err_cp: coverpoint cfg.err_inj.otp_test_tokens_valid_mubi_err;
    otp_rma_token_valid_mubi_err_cp: coverpoint cfg.err_inj.otp_rma_token_valid_mubi_err;
    token_mux_ctrl_redun_err_cp: coverpoint cfg.err_inj.token_mux_ctrl_redun_err;
    token_mux_digest_err_cp: coverpoint cfg.err_inj.token_mux_digest_err;
    jtag_csr_cp: coverpoint cfg.jtag_csr;

    // verilog_format: off - formatter doesnt like the macros here
    // Crosses for attempted second transition with and without failure
    `LC_CTRL_POST_TRANS_CROSS(err_inj)
    `LC_CTRL_POST_TRANS_CROSS(state_err)
    `LC_CTRL_POST_TRANS_CROSS(lc_fsm_backdoor_err)
    `LC_CTRL_POST_TRANS_CROSS(state_illegal_err)
    `LC_CTRL_POST_TRANS_CROSS(count_err)
    `LC_CTRL_POST_TRANS_CROSS(count_illegal_err)
    `LC_CTRL_POST_TRANS_CROSS(count_backdoor_err)

    // Crosses for error injection vs CSR access type  (JTAG/TL)- make sure we can detect
    // the error by reading the status reg via both interfaces
    `LC_CTRL_JTAG_ERROR_CROSS(clk_byp_error_rsp)
    `LC_CTRL_JTAG_ERROR_CROSS(flash_rma_error_rsp)
    `LC_CTRL_JTAG_ERROR_CROSS(otp_prog_err)
    `LC_CTRL_JTAG_ERROR_CROSS(otp_partition_err)
    `LC_CTRL_JTAG_ERROR_CROSS(token_mismatch_err)
    `LC_CTRL_JTAG_ERROR_CROSS(state_err)
    `LC_CTRL_JTAG_ERROR_CROSS(state_backdoor_err)
    `LC_CTRL_JTAG_ERROR_CROSS(lc_fsm_backdoor_err)
    `LC_CTRL_JTAG_ERROR_CROSS(kmac_fsm_backdoor_err)
    `LC_CTRL_JTAG_ERROR_CROSS(count_err)
    `LC_CTRL_JTAG_ERROR_CROSS(count_backdoor_err)
    `LC_CTRL_JTAG_ERROR_CROSS(transition_err)
    `LC_CTRL_JTAG_ERROR_CROSS(transition_count_err)
    `LC_CTRL_JTAG_ERROR_CROSS(post_trans_err)
     //verilog_format: on

  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    err_inj_cg = new();
    volatile_raw_unlock_cg = new();
  endfunction : new

  virtual function void sample_cov();
    err_inj_cg.sample();
  endfunction

endclass
