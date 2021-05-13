// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_env_cfg extends cip_base_env_cfg #(.RAL_T(pwrmgr_reg_block));

  // ext component cfgs

  `uvm_object_utils_begin(pwrmgr_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // ext interfaces
  virtual clk_rst_if slow_clk_rst_vif;

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
  endfunction

endclass
