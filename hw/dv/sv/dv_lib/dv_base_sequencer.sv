// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_sequencer #(type ITEM_T     = uvm_sequence_item,
                          type CFG_T      = dv_base_agent_cfg,
                          type RSP_ITEM_T = ITEM_T)
  extends uvm_sequencer #(.REQ(ITEM_T), .RSP(RSP_ITEM_T));

  `uvm_component_param_utils(dv_base_sequencer #(.ITEM_T     (ITEM_T),
                                                 .CFG_T      (CFG_T),
                                                 .RSP_ITEM_T (RSP_ITEM_T)))

  // These fifos collects items when req/rsp is received, which are used to communicate between
  // monitor and sequences. These fifos are optional
  // When device is re-active, it gets items from req_analysis_fifo and send rsp to driver
  // When this is a high-level agent, monitors put items to these 2 fifos for high-level seq
  uvm_tlm_analysis_fifo #(ITEM_T)     req_analysis_fifo;
  uvm_tlm_analysis_fifo #(RSP_ITEM_T) rsp_analysis_fifo;

  CFG_T cfg;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.has_req_fifo) req_analysis_fifo = new("req_analysis_fifo", this);
    if (cfg.has_rsp_fifo) rsp_analysis_fifo = new("rsp_analysis_fifo", this);
  endfunction : build_phase

endclass
