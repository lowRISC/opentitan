// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergroups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class rram_ctrl_env_cov extends cip_base_env_cov #(.CFG_T(rram_ctrl_env_cfg));
  `uvm_component_utils(rram_ctrl_env_cov)

  // Covergroups

  // Each OTP macro command (except Init), crossed with its size and its response error code.
  // Only combinations that rram_ctrl can produce are counted.
  covergroup otp_cmd_cg with function sample(otp_macro_item item);
    cmd_cp: coverpoint item.cmd {
      bins read      = {otp_ctrl_macro_pkg::Read};
      bins read_raw  = {otp_ctrl_macro_pkg::ReadRaw};
      bins write     = {otp_ctrl_macro_pkg::Write};
      bins write_raw = {otp_ctrl_macro_pkg::WriteRaw};
      bins zeroize   = {otp_ctrl_macro_pkg::Zeroize};
    }
    size_cp: coverpoint item.size {
      bins one_word   = {0};
      bins two_words  = {1};
      bins four_words = {3};
    }
    // rram_ctrl corrects single-bit errors without reporting them, so it never returns
    // MacroEccCorrError.
    err_cp: coverpoint item.err {
      bins no_error    = {otp_ctrl_macro_pkg::NoError};
      bins macro_error = {otp_ctrl_macro_pkg::MacroError};
      bins ecc_uncorr  = {otp_ctrl_macro_pkg::MacroEccUncorrError};
      bins write_blank = {otp_ctrl_macro_pkg::MacroWriteBlankError};
    }
    cmd_x_size_cross: cross cmd_cp, size_cp;
    cmd_x_err_cross: cross cmd_cp, err_cp {
      // Only an integrity check fails with MacroEccUncorrError: the one in Read, and the read-back
      // after Write and WriteRaw.
      ignore_bins no_intg_check = (binsof(cmd_cp.read_raw) || binsof(cmd_cp.zeroize)) &&
                                  binsof(err_cp.ecc_uncorr);
      // Only a write can try to clear a bit.
      ignore_bins not_a_write = (binsof(cmd_cp.read) || binsof(cmd_cp.read_raw) ||
                                 binsof(cmd_cp.zeroize)) && binsof(err_cp.write_blank);
    }
  endgroup : otp_cmd_cg

  // Standard SV/UVM methods
  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
endclass : rram_ctrl_env_cov


function rram_ctrl_env_cov::new(string name, uvm_component parent);
  super.new(name, parent);
  otp_cmd_cg = new();
endfunction : new

function void rram_ctrl_env_cov::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
  // See cip_base_env_cov for details
endfunction : build_phase
