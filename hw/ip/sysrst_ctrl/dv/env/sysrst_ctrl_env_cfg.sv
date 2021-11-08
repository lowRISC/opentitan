// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(sysrst_ctrl_reg_block));

  virtual clk_rst_if clk_aon_rst_vif;

  // ext component cfgs
  sysrst_ctrl_agent_cfg m_sysrst_ctrl_agent_cfg;

  `uvm_object_utils_begin(sysrst_ctrl_env_cfg)
    `uvm_field_object(m_sysrst_ctrl_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = sysrst_ctrl_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    // create sysrst_ctrl agent config obj
    m_sysrst_ctrl_agent_cfg = sysrst_ctrl_agent_cfg::type_id::create("m_sysrst_ctrl_agent_cfg");

    // set num_interrupts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

endclass
