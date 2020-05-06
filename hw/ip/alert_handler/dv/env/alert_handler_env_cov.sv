// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_env_cov extends cip_base_env_cov #(.CFG_T(alert_handler_env_cfg));
  `uvm_component_utils(alert_handler_env_cov)

  // the base class provides the following handles for use:
  // alert_handler_env_cfg: cfg

  // covergroups
  covergroup accum_cnt_cg with function sample (int class_i, int cnt);
    class_index_cp: coverpoint class_i {
      bins class_index[NUM_ALERT_HANDLER_CLASSES] = {[0:NUM_ALERT_HANDLER_CLASSES-1]};
    }
    accum_cnt_cp: coverpoint cnt {
      bins accum_cnt[20] = {[0:'hffff]};
      bins saturate_cnt  = {'hffff};
    }
    class_cnt_cross: cross class_index_cp, accum_cnt_cp;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // instantiate all covergroups here
    accum_cnt_cg = new();
  endfunction : new

endclass
