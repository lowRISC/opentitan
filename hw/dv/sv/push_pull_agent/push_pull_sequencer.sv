// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_sequencer #(parameter int DataWidth = 32) extends dv_base_sequencer #(
    .ITEM_T (push_pull_item#(DataWidth)),
    .CFG_T  (push_pull_agent_cfg#(DataWidth))
);
  `uvm_component_param_utils(push_pull_sequencer#(DataWidth))

  // Analysis port through which device monitors can send transactions
  // to the sequencer.
  uvm_tlm_analysis_fifo #(push_pull_item#(DataWidth)) req_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.if_mode == dv_utils_pkg::Device) begin
      req_fifo = new("req_fifo");
    end
  endfunction : build_phase

endclass
