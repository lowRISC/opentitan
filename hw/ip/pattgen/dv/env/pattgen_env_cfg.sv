// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_env_cfg extends cip_base_env_cfg #(.RAL_T(pattgen_reg_block));
  // Drain time of phase_ready_to_end
  uint ok_to_end_delay_ns = 8000;

  // Configuration for the pattgen agent (stored in the environment as m_pattgen_agent).
  rand pattgen_agent_cfg m_pattgen_agent_cfg;

  // Configuration that applies to the virtual sequences that run in the environment
  pattgen_seq_cfg seq_cfg;

  extern function new (string name="");

  // Implements a function from dv_base_env_cfg. The base class version creates RAL models. This
  // extension uses the type of the RAL model to set num_interrupts.
  extern virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);

  `uvm_object_utils_begin(pattgen_env_cfg)
    `uvm_field_object(m_pattgen_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end
endclass

function pattgen_env_cfg::new (string name="");
  super.new(name);

  list_of_alerts = pattgen_env_pkg::LIST_OF_ALERTS;

  m_pattgen_agent_cfg = pattgen_agent_cfg::type_id::create("m_pattgen_agent_cfg");
  m_pattgen_agent_cfg.if_mode = Device; // setup agent in Device mode

  seq_cfg = pattgen_seq_cfg::type_id::create("seq_cfg");
endfunction

function void pattgen_env_cfg::initialize(bit [TL_AW-1:0] csr_base_addr = '1);
  super.initialize(csr_base_addr);

  num_interrupts = ral.intr_state.get_n_used_bits();
endfunction
