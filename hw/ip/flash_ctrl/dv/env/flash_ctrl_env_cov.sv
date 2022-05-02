// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class flash_ctrl_env_cov extends cip_base_env_cov #(.CFG_T(flash_ctrl_env_cfg));
  `uvm_component_utils(flash_ctrl_env_cov)

  // the base class provides the following handles for use:
  // flash_ctrl_env_cfg: cfg

  // covergroups

  covergroup control_cg with function sample (flash_op_t flash_cfg_opts);
    part_cp : coverpoint flash_cfg_opts.partition;
    erase_cp : coverpoint flash_cfg_opts.erase_type;
    op_cp : coverpoint flash_cfg_opts.op;
    op_part_cross : cross part_cp, op_cp;
  endgroup // control_cg

  covergroup erase_susp_cg with function sample (bit erase_req = 0);
    erase_susp_cp : coverpoint erase_req {
      bins erase_susp_true = {1};
    }
  endgroup // erase_susp_cg

  function new(string name, uvm_component parent);
    super.new(name, parent);
    control_cg = new();
    erase_susp_cg = new();
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

endclass
