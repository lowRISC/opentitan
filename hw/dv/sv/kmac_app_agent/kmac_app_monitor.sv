// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_monitor extends dv_base_monitor #(.ITEM_T (kmac_app_mon_item),
                                                 .CFG_T  (kmac_app_agent_cfg),
                                                 .COV_T  (kmac_app_agent_cov));
  `uvm_component_utils(kmac_app_monitor)

  // Subsidiary analysis port that sends an item for each request word sent.
  //
  // These items are also reported (grouped into packets) in m_req_analysis_port.
  uvm_analysis_port #(kmac_app_req_item) m_req_analysis_port;

  // Subsidiary analysis port that sends an item for each request packet sent.
  //
  // The packets that are sent sent each have one or more requests which have also been reported
  // through m_req_analysis_port.
  //
  // The main analysis port for the monitor is analysis_port, which broadcasts a kmac_app_mon_item
  // for each request/response transaction. That kmac_app_mon_item will contain a copy of the
  // request packet, that has already been sent through m_req_packet_analysis_port.
  uvm_analysis_port #(kmac_app_req_packet_item) m_req_packet_analysis_port;

  extern function new (string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);

  // Declared in dv_base_monitor
  extern protected task collect_trans();

  // Collect transactions on the bus in the time between resets.
  //
  // Can be killed at any time if a reset is asserted.
  extern local task collect_between_resets();

  // Collect request transactions from the bus and add them to packet. Returns when it sees an item
  // with last=1.
  //
  // Can be killed at any time if a reset is asserted.
  extern local task populate_request_packet(kmac_app_req_packet_item packet);

  // Collect a response transaction from the bus and use it to populate rsp.
  //
  // Can be killed at any time if a reset is asserted.
  extern local task populate_response(kmac_app_rsp_item rsp);
endclass

function kmac_app_monitor::new(string name, uvm_component parent);
  super.new(name, parent);
  m_req_analysis_port = new("m_req_analysis_port", this);
  m_req_packet_analysis_port = new("m_req_packet_analysis_port", this);
endfunction

task kmac_app_monitor::run_phase(uvm_phase phase);
  fork
    super.run_phase(phase);
    begin
      // Make sure that in_reset is correct at the start of the phase, then check that we are
      // genuinely in reset by the start of the loop.
      cfg.in_reset = (cfg.vif.rst_ni !== 1'b1);
      wait(!cfg.vif.rst_ni);

      forever begin
        cfg.in_reset = 1;

        // Set ok_to_end, which may have been cleared by collect_between_resets if it saw a KMAC
        // request that hadn't had a response when reset was asserted.
        ok_to_end = 1;

        wait (cfg.vif.rst_ni);

        cfg.in_reset = 0;
        wait (!cfg.vif.rst_ni);
      end
    end
  join
endtask

task kmac_app_monitor::collect_trans();
  // At the start of the simulation, wait to see rst_ni===1. We don't have to do this later in the
  // run, but have to check here to avoid a race against the reset tracking in run_phase at the
  // start of time.
  wait (cfg.vif.rst_ni);

  forever begin
    wait(!cfg.in_reset);
    fork : isolation_fork begin
      fork
        wait(cfg.in_reset);
        collect_between_resets();
      join_any
      disable fork;
    end join
  end
endtask

task kmac_app_monitor::collect_between_resets();
  forever begin
    kmac_app_mon_item item = kmac_app_mon_item::type_id::create("item");
    populate_request_packet(item.m_req);

    // Broadcast the packet that we have now collected.
    m_req_packet_analysis_port.write(item.m_req);

    // Clear ok_to_end so that the simulation doesn't finish until a response has come back
    ok_to_end = 0;

    populate_response(item.m_rsp);

    ok_to_end = 1;
    analysis_port.write(item);
  end
endtask

task kmac_app_monitor::populate_request_packet(kmac_app_req_packet_item packet);
  forever begin
    kmac_app_req_item req;

    while(! (cfg.vif.mon_cb.req_valid && cfg.vif.mon_cb.req_ready)) @(cfg.vif.mon_cb);

    req = kmac_app_req_item::type_id::create("req");
    req.m_data = cfg.vif.mon_cb.req_data;
    // A correct strb value should be of the form (1 << k) - 1. This is actually checked with an
    // assertion in kmac_app_if. To convert back to the number of bytes, add one (to get 1 << k) and
    // call $clog2.
    //
    // Note that if strb=0 thon we will call $clog2(1) = 0, which is the value we want.
    req.m_num_bytes = $clog2(cfg.vif.mon_cb.req_strb + 1);
    req.m_last = cfg.vif.mon_cb.req_last;

    // Broadcast the request to m_req_analysis_port and add it to the packet that we are populating.
    m_req_analysis_port.write(req);
    packet.m_reqs.push_back(req);

    // If this was the last word of the packet, we are done.
    if (cfg.vif.mon_cb.req_last) break;

    // Otherwise, go past the item before waiting for the next.
    @(cfg.vif.mon_cb);
  end
endtask

task kmac_app_monitor::populate_response(kmac_app_rsp_item rsp);
  while (cfg.vif.mon_cb.rsp_done !== 1'b1) @(cfg.vif.mon_cb);
  rsp.m_digest_share0 = cfg.vif.mon_cb.rsp_digest_share0;
  rsp.m_digest_share1 = cfg.vif.mon_cb.rsp_digest_share1;
  rsp.m_error = cfg.vif.mon_cb.rsp_error;
endtask
