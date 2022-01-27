// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_env_cfg extends cip_base_env_cfg #(.RAL_T(rv_dm_reg_block));

  // ext component cfgs
  rand jtag_agent_cfg m_jtag_agent_cfg;

  `uvm_object_utils_begin(rv_dm_env_cfg)
    `uvm_field_object(m_jtag_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = rv_dm_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
    // create jtag agent config obj
    m_jtag_agent_cfg = jtag_agent_cfg::type_id::create("m_jtag_agent_cfg");
  endfunction

endclass
