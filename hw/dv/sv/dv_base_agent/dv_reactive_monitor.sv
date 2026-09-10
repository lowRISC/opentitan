// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_reactive_monitor #(type ITEM_T = uvm_sequence_item,
                            type REQ_ITEM_T = ITEM_T,
                            type RSP_ITEM_T = ITEM_T,
                            type CFG_T = dv_base_agent_cfg,
                            type COV_T = dv_base_agent_cov)
  extends dv_base_monitor #(.ITEM_T(ITEM_T), .CFG_T(CFG_T), .COV_T(COV_T));

  `uvm_component_param_utils(dv_reactive_monitor #(ITEM_T, REQ_ITEM_T, RSP_ITEM_T, CFG_T, COV_T))

  // item will be sent to this port for seq when req phase is done (last is set)
  uvm_analysis_port #(REQ_ITEM_T) req_analysis_port;
  // item will be sent to this port for seq when rsp phase is done (rsp_done is set)
  uvm_analysis_port #(RSP_ITEM_T) rsp_analysis_port;

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
endclass

function dv_reactive_monitor::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void dv_reactive_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  req_analysis_port = new("req_analysis_port", this);
  rsp_analysis_port = new("rsp_analysis_port", this);
endfunction
