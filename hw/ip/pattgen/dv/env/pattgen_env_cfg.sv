// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_env_cfg extends cip_base_env_cfg #(.RAL_T(pattgen_reg_block));
  // drained time of phase_ready_to_end
  uint ok_to_end_delay_ns = 8000;

  // pattgen_agent_cfg
  rand pattgen_agent_cfg m_pattgen_agent_cfg;
  
  // seq cfg
  pattgen_seq_cfg seq_cfg;

  `uvm_object_utils_begin(pattgen_env_cfg)
    `uvm_field_object(m_pattgen_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end
  
  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);

    // create pattgen_agent_cfg
    m_pattgen_agent_cfg = pattgen_agent_cfg::type_id::create("m_pattgen_agent_cfg");
    m_pattgen_agent_cfg.if_mode = Device; // setup agent in Device mode

    // create the seq_cfg
    seq_cfg = pattgen_seq_cfg::type_id::create("seq_cfg");

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction
endclass : pattgen_env_cfg
