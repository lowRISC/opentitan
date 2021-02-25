// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_env_cfg extends cip_base_env_cfg #(.RAL_T(edn_reg_block));

  // ext component cfgs
  rand csrng_agent_cfg   m_csrng_agent_cfg;
  rand push_pull_agent_cfg#(.HostDataWidth(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH))
            m_endpoint_agent_cfg [NUM_ENDPOINTS:0];

  `uvm_object_utils_begin(edn_env_cfg)
    `uvm_field_object(m_csrng_agent_cfg, UVM_DEFAULT)
    for (int i = 0; i < NUM_ENDPOINTS; i++) begin
      `uvm_field_object(m_endpoint_agent_cfg[i], UVM_DEFAULT)
    end
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
    // create config objects
    m_csrng_agent_cfg = csrng_agent_cfg::type_id::create("m_csrng_genbits_agent_cfg");

    for (int i = 0; i < NUM_ENDPOINTS; i++) begin
      m_endpoint_agent_cfg[i] = push_pull_agent_cfg#(.HostDataWidth(edn_pkg::
                                FIPS_ENDPOINT_BUS_WIDTH))::type_id::create
                                ($sformatf("m_endpoint_agent_cfg[%0d]", i));
    end

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

endclass
