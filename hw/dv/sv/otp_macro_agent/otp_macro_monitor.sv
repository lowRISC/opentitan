// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Watches otp_macro_if and publishes each completed transaction (request plus response) on
// analysis_port.
//
// A request is recorded when it is accepted (req.valid && rsp.ready). Responses come back in
// order, so each rsp.rvalid pulse completes the oldest recorded request.
//
// The monitor also maintains cfg.in_reset from the interface's reset.
class otp_macro_monitor extends dv_base_monitor #(
  .ITEM_T (otp_macro_item),
  .CFG_T  (otp_macro_agent_cfg)
);
  `uvm_component_utils(otp_macro_monitor)

  // Accepted requests that have not had their response yet, oldest first.
  protected otp_macro_item m_pending[$];

  extern function new(string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);
  extern virtual task monitor_ready_to_end();

  // Keeps cfg.in_reset in sync with the interface's reset.
  extern protected virtual task monitor_reset();

  extern protected virtual task collect_trans();
endclass : otp_macro_monitor

function otp_macro_monitor::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

task otp_macro_monitor::run_phase(uvm_phase phase);
  fork
    monitor_reset();
    super.run_phase(phase);
  join
endtask : run_phase

task otp_macro_monitor::monitor_reset();
  forever begin
    // Anything other than a clean 1 (including X at time zero) counts as reset.
    cfg.in_reset = 1'b1;
    wait (cfg.vif.rst_n === 1'b1);
    cfg.in_reset = 1'b0;
    wait (cfg.vif.rst_n !== 1'b1);
  end
endtask : monitor_reset

task otp_macro_monitor::collect_trans();
  forever begin
    @(cfg.vif.mon_cb);
    if (cfg.in_reset) begin
      m_pending.delete();
      continue;
    end

    // Handle a response before a new request: an rvalid in this cycle can only belong to a
    // request that was accepted in an earlier cycle.
    if (cfg.vif.mon_cb.rsp.rvalid) begin
      otp_macro_item item;
      `DV_CHECK_FATAL(m_pending.size() > 0, "rvalid with no outstanding request")
      item       = m_pending.pop_front();
      item.rdata = cfg.vif.mon_cb.rsp.rdata;
      item.err   = cfg.vif.mon_cb.rsp.err;
      `uvm_info(`gfn, $sformatf("Transaction complete:\n%0s", item.sprint()), UVM_HIGH)
      analysis_port.write(item);
    end

    if (cfg.vif.mon_cb.req.valid && cfg.vif.mon_cb.rsp.ready) begin
      otp_macro_item item = otp_macro_item::type_id::create("item");
      item.cmd   = cfg.vif.mon_cb.req.cmd;
      item.size  = cfg.vif.mon_cb.req.size;
      item.addr  = cfg.vif.mon_cb.req.addr;
      item.wdata = cfg.vif.mon_cb.req.wdata;
      m_pending.push_back(item);
    end
  end
endtask : collect_trans

task otp_macro_monitor::monitor_ready_to_end();
  forever begin
    ok_to_end = (m_pending.size() == 0) && !cfg.vif.mon_cb.req.valid;
    @(cfg.vif.mon_cb);
  end
endtask : monitor_ready_to_end
