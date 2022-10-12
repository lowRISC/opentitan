// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_xht_monitor extends dv_base_monitor #(
  .ITEM_T (entropy_src_xht_item),
  .CFG_T  (entropy_src_xht_agent_cfg),
  .COV_T  (dv_base_agent_cov#(entropy_src_xht_agent_cfg))
);

  `uvm_component_utils(entropy_src_xht_monitor)
  `uvm_component_new

  task run_phase(uvm_phase phase);
    fork
      monitor_reset();
      begin
        @(posedge cfg.vif.rst_n);
        collect_req(phase);
      end
    join
  endtask

  virtual protected task monitor_reset();
    forever begin
      @(negedge cfg.vif.rst_n);
      `uvm_info(`gfn, "Reset detected!", UVM_DEBUG)
      cfg.in_reset = 1;
      @(posedge cfg.vif.rst_n);
      `uvm_info(`gfn, "Reset release detected!", UVM_DEBUG)
      cfg.in_reset = 0;
    end
  endtask

  // Shorthand for restarting forever loop on reset detection.
  `define WAIT_FOR_RESET    \
    if (cfg.in_reset) begin \
      wait (!cfg.in_reset); \
      continue;             \
    end

  virtual protected task collect_req(uvm_phase phase);
    forever begin
      @(cfg.vif.mon_cb);
      `WAIT_FOR_RESET
      create_and_write_item();
    end
  endtask

  virtual protected function void create_and_write_item();
    entropy_src_xht_item item;

    bit  event_filter;

    // The entropy_src_extht_req_t encodes three types of events that the agent must monitor
    // - entropy_bit_valid
    // - clear, and
    // - window_wrap pulse.
    // All other req fields are data or parameters (unchanging except with a clear pulse)
    //
    // Meanwhile the entropy_src_rsp_t data is continuously monitored.
    // Creating a new item at every clock however has a noticible performance impact on simulations
    // therefore we typically assume that the xht_sequence only outputs updates in the cycle after
    // entropy_bit_valid, and so we add entropy_bit_valid_q to our event filter.
    //
    // To get scoreboard access to all bus samples, set cfg.unfiltered_monitor_traffic to 1. This
    // will allow for simulations in which an xht sequence takes longer than one cycle to respond.
    event_filter = (cfg.vif.mon_cb.req.entropy_bit_valid ||
                    cfg.vif.mon_cb.req.clear ||
                    cfg.vif.mon_cb.req.window_wrap_pulse ||
                    cfg.vif.mon_cb.entropy_bit_valid_q);

    if (cfg.unfiltered_monitor_traffic || event_filter) begin
      `uvm_info(`gfn, "Sending item", UVM_DEBUG)
      item = entropy_src_xht_item::type_id::create("item");
      item.rsp = cfg.vif.mon_cb.rsp;
      item.req = cfg.vif.mon_cb.req;
      analysis_port.write(item);
      req_analysis_port.write(item);
    end
  endfunction

endclass
