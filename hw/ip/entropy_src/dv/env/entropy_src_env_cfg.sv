// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_env_cfg extends cip_base_env_cfg #(.RAL_T(entropy_src_reg_block));

  `uvm_object_utils_begin(entropy_src_env_cfg)
  `uvm_object_utils_end

  // ext component cfgs
  rand push_pull_agent_cfg#(RNG_DATA_WIDTH)     m_rng_agent_cfg;
  rand push_pull_agent_cfg#(CSRNG_DATA_WIDTH)   m_csrng_agent_cfg;
  
  virtual pins_if                  efuse_es_sw_reg_en_vif;

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = entropy_src_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    // create agent config objs
    m_rng_agent_cfg   = push_pull_agent_cfg#(RNG_DATA_WIDTH)::type_id::create("m_rng_agent_cfg");
    m_csrng_agent_cfg = push_pull_agent_cfg#(CSRNG_DATA_WIDTH)::type_id::create("m_csrng_agent_cfg");

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

endclass
