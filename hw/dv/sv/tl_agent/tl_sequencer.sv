// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class tl_sequencer extends uvm_sequencer#(tl_seq_item);
  `uvm_component_utils(tl_sequencer)

  uvm_tlm_analysis_fifo#(tl_seq_item) a_chan_req_fifo;
  tl_agent_cfg cfg;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    a_chan_req_fifo = new("a_chan_req_fifo", this);
  endfunction : build_phase

endclass : tl_sequencer
