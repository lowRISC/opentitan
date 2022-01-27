// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class dm_env extends uvm_env;

  rjtag_agent m_agt;

  `uvm_component_utils(dm_env)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_agt = rjtag_agent::type_id::create("m_agt", this);
  endfunction : build_phase

endclass : dm_env
