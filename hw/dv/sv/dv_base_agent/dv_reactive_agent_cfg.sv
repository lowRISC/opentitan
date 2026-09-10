// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The base config object for a reactive agent

class dv_reactive_agent_cfg extends dv_base_agent_cfg;

  // True if agent's sequencer has a request fifo. If so, the agent will connect its monitor's
  // req_analysis_port to the sequencer's request fifo.
  bit has_req_fifo = 1'b0;

  // True if agent's sequencer has a response fifo. If so, the agent will connect its monitor's
  // req_analysis_port to the sequencer's response fifo.
  bit has_rsp_fifo = 1'b0;

  `uvm_object_utils_begin(dv_reactive_agent_cfg)
    `uvm_field_int (has_req_fifo, UVM_DEFAULT)
    `uvm_field_int (has_rsp_fifo, UVM_DEFAULT)
  `uvm_object_utils_end

  extern function new (string name="");
endclass

function dv_reactive_agent_cfg::new (string name="");
  super.new(name);
endfunction
