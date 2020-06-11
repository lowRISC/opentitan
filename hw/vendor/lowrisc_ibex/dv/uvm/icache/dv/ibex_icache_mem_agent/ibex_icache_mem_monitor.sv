// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_mem_monitor
  extends dv_base_monitor #(.ITEM_T (ibex_icache_mem_bus_item),
                            .CFG_T  (ibex_icache_mem_agent_cfg),
                            .COV_T  (ibex_icache_mem_agent_cov));

  `uvm_component_utils(ibex_icache_mem_monitor)
  `uvm_component_new

  // the base class provides the following handles for use:
  // ibex_icache_mem_agent_cfg: cfg
  // ibex_icache_mem_agent_cov: cov
  // uvm_analysis_port #(ibex_icache_mem_bus_item): analysis_port

  // Incoming requests. This gets hooked up to the sequencer to service requests
  uvm_analysis_port #(ibex_icache_mem_req_item) request_port;

  function automatic void build_phase(uvm_phase phase);
    super.build_phase(phase);
    request_port = new("request_port", this);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask

  // Collect transactions forever. Forked in dv_base_moditor::run_phase
  protected task automatic collect_trans(uvm_phase phase);
    fork
      collect_requests();
      collect_grants();
      collect_responses();
    join
  endtask

  // The collect_requests monitor is in charge of spotting changes to instr_addr_o when the req
  // line is high
  //
  // This must collect the "I have a new address request" immediately, rather than at the next clock
  // edge, to make sure that a PMP error can be signalled in the same cycle.
  //
  // Note that it's possible the underlying memory seed will change after the request has been seen.
  // We don't try to spot this, and instead report the error state based on the seed when the
  // request appeared.
  task automatic collect_requests();
    forever begin
      // At this point, req will be low. Wait for a posedge (the first request).
      @(posedge cfg.vif.req);

      // There will now be 1 or more "request events" while the request line remains high. Report
      // each to the sequence.
      while (cfg.vif.req) begin

        // Wait between seeing the request and looking for a seed. It's a bit sad not to have a
        // cleverer bit of synchronization, but the problem is that the core can decide to send us a
        // new seed and do the second of 2 back-to-back branches to the same address, both at the
        // same time. Without this delay, we might get here (via the grant event) before the core
        // sends the new seed.
        #1step;

        // Check that the request didn't go away while we were waiting.
        if (!cfg.vif.req) break;

        new_request(cfg.vif.addr);

        // Now wait for the end of the request, which is caused by a drop in req, a change in
        // address or the request being seen (positive clock edge with gnt=1). In the final case,
        // this should be treated as a back-to-back request.
        @(negedge cfg.vif.req or cfg.vif.addr or posedge cfg.vif.clk);
      end
    end
  endtask

  // The collect_grants monitor is in charge of spotting granted requests which haven't been
  // squashed by a PMP error, passing them back to the driver ("Hey, you granted this. Time to
  // service it!")
  task automatic collect_grants();
    logic pending_req = 1'b0;

    forever begin
      if (cfg.vif.monitor_cb.req && cfg.vif.monitor_cb.gnt && !cfg.vif.monitor_cb.pmp_err) begin
        new_grant(cfg.vif.monitor_cb.addr);
      end
      if (cfg.en_cov && cfg.vif.monitor_cb.gnt) cov.gnt_err_cg.sample(cfg.vif.monitor_cb.pmp_err);

      @(cfg.vif.monitor_cb);
    end
  endtask

  task automatic collect_responses();
    ibex_icache_mem_bus_item bus_trans;

    forever begin
      if (cfg.vif.monitor_cb.rvalid) begin
        bus_trans = ibex_icache_mem_bus_item::type_id::create("bus_trans");
        bus_trans.is_grant = 1'b0;
        bus_trans.data     = cfg.vif.monitor_cb.rdata;
        bus_trans.err      = cfg.vif.monitor_cb.err;
        analysis_port.write(bus_trans);
      end

      @(cfg.vif.monitor_cb);
    end
  endtask

  // This is called immediately when an address is requested and is used to drive the PMP response.
  function automatic void new_request(logic [31:0] addr);
    ibex_icache_mem_req_item item = new("item");

    item.is_grant = 1'b0;
    item.address = addr;
    request_port.write(item);
  endfunction

  // This is called on a clock edge when an request is granted
  function automatic void new_grant(logic [31:0] addr);
    ibex_icache_mem_req_item item;
    ibex_icache_mem_bus_item bus_trans;

    item = ibex_icache_mem_req_item::type_id::create("item");
    item.is_grant = 1'b1;
    item.address  = addr;
    request_port.write(item);

    bus_trans = ibex_icache_mem_bus_item::type_id::create("bus_trans");
    bus_trans.is_grant = 1'b1;
    bus_trans.data     = addr;
    bus_trans.err      = 0;
    analysis_port.write(bus_trans);
  endfunction

endclass
