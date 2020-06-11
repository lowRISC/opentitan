// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequencer class for the icache memory agent.

class ibex_icache_mem_sequencer
  extends dv_base_sequencer #(.ITEM_T (ibex_icache_mem_resp_item),
                              .CFG_T  (ibex_icache_mem_agent_cfg));

  `uvm_component_utils(ibex_icache_mem_sequencer)
  `uvm_component_new

  uvm_tlm_analysis_fifo #(ibex_icache_mem_req_item) request_fifo;
  uvm_tlm_analysis_fifo #(bit [31:0])               seed_fifo;

  // An objection used for heartbeat tracking. Set with register_hb.
  uvm_callbacks_objection hb_objection;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    request_fifo = new("request_fifo", this);
    seed_fifo    = new("seed_fifo", this);
  endfunction

  function void register_hb (uvm_callbacks_objection obj);
    hb_objection = obj;
  endfunction

  virtual function void send_request(uvm_sequence_base sequence_ptr,
                                     uvm_sequence_item t,
                                     bit rerandomize = 0);
    if (hb_objection != null)
      hb_objection.raise_objection(this);

    super.send_request(sequence_ptr, t, rerandomize);
  endfunction

endclass
