// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_sequencer extends dv_base_sequencer#(i2c_item, i2c_agent_cfg);
  `uvm_component_utils(i2c_sequencer)

  uvm_tlm_analysis_fifo #(i2c_item) mon_item_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon_item_fifo = new("mon_item_fifo", this);
  endfunction : build_phase

endclass : i2c_sequencer
