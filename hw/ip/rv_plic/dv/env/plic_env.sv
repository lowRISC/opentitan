// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

class plic_env extends uvm_env;

  tl_agent m_tlagt;
  irq_agent #(32) m_irqagt;

  `uvm_component_utils(plic_env)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_tlagt = tl_agent::type_id::create("m_tlagt", this);
    m_irqagt = irq_agent::type_id::create("m_irqagt", this);

    uvm_config_db #(uvm_object_wrapper)::set(
      this,
      "m_irqagt.m_seqr.main_phase",
      "default_sequence",
      irq_sequence::type_id::get());
  endfunction : build_phase

endclass : plic_env
