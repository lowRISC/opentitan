// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(lc_ctrl_reg_block));

  // ext component cfgs
  // ext interfaces
  pwr_lc_vif  pwr_lc_vif;
  lc_ctrl_vif lc_ctrl_vif;

  `uvm_object_utils_begin(lc_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = lc_ctrl_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
  endfunction

endclass
