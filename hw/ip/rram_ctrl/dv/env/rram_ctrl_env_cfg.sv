// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(rram_ctrl_reg_block));

  // ext component cfgs
  rand tl_csr_agent_cfg m_tl_csr_agent_cfg;
  rand tl_host_agent_cfg m_tl_host_agent_cfg;
  rand tl_prim_agent_cfg m_tl_prim_agent_cfg;

  `uvm_object_utils_begin(rram_ctrl_env_cfg)
    `uvm_field_object(m_tl_csr_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(m_tl_host_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(m_tl_prim_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = rram_ctrl_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
    // create tl_csr agent config obj
    m_tl_csr_agent_cfg = tl_csr_agent_cfg::type_id::create("m_tl_csr_agent_cfg");
    // create tl_host agent config obj
    m_tl_host_agent_cfg = tl_host_agent_cfg::type_id::create("m_tl_host_agent_cfg");
    // create tl_prim agent config obj
    m_tl_prim_agent_cfg = tl_prim_agent_cfg::type_id::create("m_tl_prim_agent_cfg");

    // set num_interrupts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

endclass
