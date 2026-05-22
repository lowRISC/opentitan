// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_reactive_sequencer #(type ITEM_T     = uvm_sequence_item,
                              type CFG_T      = dv_reactive_agent_cfg,
                              type RSP_ITEM_T = ITEM_T)
  extends dv_base_sequencer #(.ITEM_T(ITEM_T), .CFG_T(CFG_T), .RSP_ITEM_T(RSP_ITEM_T));

  `uvm_component_param_utils(dv_reactive_sequencer #(.ITEM_T     (ITEM_T),
                                                     .CFG_T      (CFG_T),
                                                     .RSP_ITEM_T (RSP_ITEM_T)))

  // These FIFOs collect items when req/rsp is received, which are used to communicate between
  // monitor and sequences. These FIFOs are only created if has_req_fifo / has_rsp_fifo is true in
  // the agent config.
  //
  // When device is reactive, it gets items from req_analysis_fifo and send rsp to driver When this
  // is a high-level agent, monitors put items to these 2 FIFOs for high-level seq
  uvm_tlm_analysis_fifo #(ITEM_T)     req_analysis_fifo;
  uvm_tlm_analysis_fifo #(RSP_ITEM_T) rsp_analysis_fifo;

  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
endclass

function dv_reactive_sequencer::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void dv_reactive_sequencer::build_phase(uvm_phase phase);
  super.build_phase(phase);

  if (cfg == null) `uvm_fatal(get_full_name(), "agent cfg not provided.")

  if (cfg.has_req_fifo) req_analysis_fifo = new("req_analysis_fifo", this);
  if (cfg.has_rsp_fifo) rsp_analysis_fifo = new("rsp_analysis_fifo", this);
endfunction
