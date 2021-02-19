// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_sequencer extends dv_base_sequencer #(
    .ITEM_T (keymgr_kmac_item),
    .CFG_T  (keymgr_kmac_agent_cfg)
);
  `uvm_component_param_utils(keymgr_kmac_sequencer)

  push_pull_sequencer#(`CONNECT_DATA_WIDTH) m_push_pull_sequencer;

  // Analysis port through which device monitors can send transactions
  // to the sequencer.
  uvm_tlm_analysis_fifo #(keymgr_kmac_item) req_data_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.if_mode == dv_utils_pkg::Device) begin
      req_data_fifo = new("req_data_fifo", this);
    end
  endfunction : build_phase

endclass
