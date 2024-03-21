// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_mem_monitor
  extends dv_base_monitor #(.ITEM_T     (ibex_icache_mem_bus_item),
                            .REQ_ITEM_T (ibex_icache_mem_resp_item),
                            .RSP_ITEM_T (ibex_icache_mem_resp_item),
                            .CFG_T      (ibex_icache_mem_agent_cfg),
                            .COV_T      (ibex_icache_mem_agent_cov));

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
      collect_grants();
      collect_responses();
    join
  endtask

  // The collect_grants monitor is in charge of spotting granted requests, passing them back to the
  // driver ("Hey, you granted this. Time to service it!")
  task automatic collect_grants();
    logic pending_req = 1'b0;

    forever begin
      if (cfg.vif.monitor_cb.req && cfg.vif.monitor_cb.gnt) begin
        new_grant(cfg.vif.monitor_cb.addr);
      end

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

  // This is called on a clock edge when an request is granted
  function automatic void new_grant(logic [31:0] addr);
    ibex_icache_mem_req_item item;
    ibex_icache_mem_bus_item bus_trans;

    item = ibex_icache_mem_req_item::type_id::create("item");
    item.address  = addr;
    request_port.write(item);

    bus_trans = ibex_icache_mem_bus_item::type_id::create("bus_trans");
    bus_trans.is_grant = 1'b1;
    bus_trans.data     = addr;
    bus_trans.err      = 0;
    analysis_port.write(bus_trans);
  endfunction

endclass
