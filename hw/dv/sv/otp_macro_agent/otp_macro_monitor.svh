// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Monitor that spots completed transactions on otp_macro_if
//
// A request is recorded when it is accepted (req.valid && rsp.ready). Responses come back in
// order, so each rsp.rvalid pulse completes the oldest recorded request. The completed transaction
// is written to analysis_port as an otp_macro_rsp_seq_item, holding its request in m_req.
//
// Note that ok_to_end tracking is done in collect_between_resets, rather than in a
// monitor_ready_to_end task (as expected by dv_base_monitor). This makes it easier to link to the
// requests that are still waiting for a response, which collect_between_resets already tracks.

class otp_macro_monitor extends dv_base_monitor #(.ITEM_T (otp_macro_rsp_seq_item),
                                                  .CFG_T  (otp_macro_agent_cfg));
  `uvm_component_utils(otp_macro_monitor)

  extern function new (string name, uvm_component parent);

  // Collect transactions forever. This implements a task from dv_base_monitor.
  extern virtual protected task collect_trans();

  // Collect requests and responses, writing completed transactions to the analysis port. Will be
  // killed if reset is asserted, which drops any request still waiting for its response.
  extern local task collect_between_resets();
endclass

function otp_macro_monitor::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

task otp_macro_monitor::collect_trans();
  wait (!$isunknown(cfg.m_vif.rst_ni));
  cfg.in_reset = !cfg.m_vif.rst_ni;
  forever begin
    wait (cfg.m_vif.rst_ni);
    cfg.in_reset = 0;
    fork : isolation_fork begin
      fork
        wait (!cfg.m_vif.rst_ni);
        collect_between_resets();
      join_any
      disable fork;
    end join

    cfg.in_reset = 1;
    ok_to_end = 1;
  end
endtask

task otp_macro_monitor::collect_between_resets();
  // Accepted requests that have not had their response yet, oldest first.
  otp_macro_req_seq_item pending[$];

  forever begin
    // Only wake up on a clock edge where something happens.
    @(cfg.m_vif.mon_cb iff (cfg.m_vif.mon_cb.rsp.rvalid ||
                            (cfg.m_vif.mon_cb.req.valid && cfg.m_vif.mon_cb.rsp.ready)));

    // Handle a response before a new request: an rvalid in this cycle can only belong to a request
    // that was accepted in an earlier cycle.
    if (cfg.m_vif.mon_cb.rsp.rvalid) begin
      if (pending.size() == 0) begin
        `uvm_error("stray_rvalid", "Response with no outstanding request.")
      end else begin
        otp_macro_rsp_seq_item rsp = otp_macro_rsp_seq_item::type_id::create("rsp");
        rsp.m_req   = pending.pop_front();
        rsp.m_rdata = cfg.m_vif.mon_cb.rsp.rdata;
        rsp.m_err   = cfg.m_vif.mon_cb.rsp.err;
        `uvm_info("trans", $sformatf("Transaction complete:\n%0s", rsp.sprint()), UVM_HIGH)
        analysis_port.write(rsp);
      end
    end

    if (cfg.m_vif.mon_cb.req.valid && cfg.m_vif.mon_cb.rsp.ready) begin
      otp_macro_req_seq_item req = otp_macro_req_seq_item::type_id::create("req");
      req.m_cmd   = cfg.m_vif.mon_cb.req.cmd;
      req.m_size  = cfg.m_vif.mon_cb.req.size;
      req.m_addr  = cfg.m_vif.mon_cb.req.addr;
      req.m_wdata = cfg.m_vif.mon_cb.req.wdata;
      pending.push_back(req);
    end

    ok_to_end = (pending.size() == 0) && !cfg.m_vif.mon_cb.req.valid;
  end
endtask
