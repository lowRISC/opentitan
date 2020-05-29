// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_core_sequencer
  extends dv_base_sequencer #(.ITEM_T     (ibex_icache_core_req_item),
                              .RSP_ITEM_T (ibex_icache_core_rsp_item),
                              .CFG_T      (ibex_icache_core_agent_cfg));
  `uvm_component_utils(ibex_icache_core_sequencer)
  `uvm_component_new

  // An objection used for heartbeat tracking. Set with register_hb.
  uvm_callbacks_objection hb_objection;

  function void register_hb (uvm_callbacks_objection obj);
    hb_objection = obj;
  endfunction

  virtual function void send_request(uvm_sequence_base sequence_ptr,
                                     uvm_sequence_item t,
                                     bit rerandomize = 0);
    if (hb_objection != null) begin
      hb_objection.raise_objection(this);
    end

    super.send_request(sequence_ptr, t, rerandomize);
  endfunction

endclass
