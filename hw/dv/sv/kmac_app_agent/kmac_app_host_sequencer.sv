// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_host_sequencer extends dv_base_sequencer #(.ITEM_T (kmac_app_req_item),
                                                          .CFG_T (kmac_app_agent_cfg));
  `uvm_component_utils(kmac_app_host_sequencer)

  uvm_tlm_analysis_fifo #(kmac_app_rsp_item) m_rsp_fifo;

  extern function new(string name, uvm_component parent);
endclass

function kmac_app_host_sequencer::new(string name, uvm_component parent);
  super.new(name, parent);
  m_rsp_fifo = new("m_rsp_fifo", this);
endfunction