// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// A simple subclass of dv_base_monitor, which adds a req_analysis_port and rsp_analysis_port. These
// can be connected to the sequencer's req/rsp analysis FIFOs to allow the monitor to easily pair up
// bus transactions that it has seen with the sequence items that caused them.
//

class dv_seq_monitor #(type ITEM_T = uvm_sequence_item,
                       type REQ_ITEM_T = ITEM_T,
                       type RSP_ITEM_T = ITEM_T,
                       type CFG_T  = dv_seq_agent_cfg,
                       type COV_T  = dv_base_agent_cov)
  extends dv_base_monitor #(.ITEM_T (ITEM_T), .CFG_T (CFG_T), .COV_T (COV_T));

  `uvm_component_param_utils(dv_seq_monitor #(ITEM_T, REQ_ITEM_T, RSP_ITEM_T, CFG_T, COV_T))

  // item will be sent to this port for seq when req phase is done (last is set)
  uvm_analysis_port #(REQ_ITEM_T) req_analysis_port;
  // item will be sent to this port for seq when rsp phase is done (rsp_done is set)
  uvm_analysis_port #(RSP_ITEM_T) rsp_analysis_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    req_analysis_port = new("req_analysis_port", this);
    rsp_analysis_port = new("rsp_analysis_port", this);
  endfunction

endclass
