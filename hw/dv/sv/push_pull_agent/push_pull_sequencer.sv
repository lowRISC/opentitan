// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_sequencer #(parameter int HostDataWidth = 32,
                            parameter int DeviceDataWidth = HostDataWidth)
  extends dv_base_sequencer #(
    .ITEM_T (push_pull_item#(HostDataWidth, DeviceDataWidth)),
    .CFG_T  (push_pull_agent_cfg#(HostDataWidth, DeviceDataWidth))
);
  `uvm_component_param_utils(push_pull_sequencer#(HostDataWidth, DeviceDataWidth))

  // Analysis port through which device monitors can send transactions
  // to the sequencer.
  uvm_tlm_analysis_fifo #(push_pull_item#(HostDataWidth, DeviceDataWidth)) push_pull_req_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.if_mode == dv_utils_pkg::Device) begin
      push_pull_req_fifo = new("push_pull_req_fifo", this);
    end
  endfunction : build_phase

endclass
