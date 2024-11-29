// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Use this UVM macro as we may need to implement multiple uvm_analysis_imp, which means
// implemneting multiple write methods which is not possible with the same name.
`uvm_analysis_imp_decl(_sqr_reset)

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

  uvm_analysis_imp_sqr_reset #(
    reset_state_e, dv_base_sequencer#(ITEM_T,CFG_T,RSP_ITEM_T)) reset_st_imp;

  function new (string name="", uvm_component parent=null);
    super.new(name, parent);
    reset_st_imp = new ("reset_st_imp", this);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.has_req_fifo) req_analysis_fifo = new("req_analysis_fifo", this);
    if (cfg.has_rsp_fifo) rsp_analysis_fifo = new("rsp_analysis_fifo", this);
  endfunction : build_phase

  // This function will be executed each time the reset monitor will detect a reset activity. As
  // the monitor will broadcast this activity on a UVM TLM port uvm_analysis_port which is connected
  // to this component via a UVM analysis import.
  virtual function void write_sqr_reset(reset_state_e reset_st);
    if (reset_st == ResetAsserted) begin
      // stop_sequences();
    end
    `uvm_info(`gtn, $sformatf("Update reset state to %0s", reset_st.name()), UVM_DEBUG)
  endfunction : write_sqr_reset

endclass
