// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(sysrst_ctrl_reg_block));

  // ext component cfgs
  virtual sysrst_ctrl_if vif;
  virtual clk_rst_if clk_aon_rst_vif;

  `uvm_object_utils_begin(sysrst_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = sysrst_ctrl_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    // set num_interrupts
    num_interrupts = ral.intr_state.get_n_used_bits();

    // only support 1 outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction

endclass
