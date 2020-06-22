// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_core_monitor extends dv_base_monitor #(
    .ITEM_T (ibex_icache_core_bus_item),
    .CFG_T  (ibex_icache_core_agent_cfg),
    .COV_T  (ibex_icache_core_agent_cov)
  );
  `uvm_component_utils(ibex_icache_core_monitor)

  // the base class provides the following handles for use:
  // ibex_icache_core_agent_cfg: cfg
  // ibex_icache_core_agent_cov: cov
  // uvm_analysis_port #(ibex_icache_core_bus_item): analysis_port

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    if (cfg.en_cov) begin
      fork
        process_cancelled_valid();
      join_none
    end

    super.run_phase(phase);

    disable fork;
  endtask

  // collect transactions forever - already forked in dv_base_moditor::run_phase
  virtual protected task collect_trans(uvm_phase phase);
    ibex_icache_core_bus_item trans;
    logic                     last_inval = 0;
    logic                     last_enable = 0;
    logic                     last_busy = 0;
    logic [31:0]              last_addr = 'x;

    forever begin
      // Collect events on positive clock edges. We collect "outputs" from the cache first, and then
      // "inputs". This makes the scoreboard's job easier: if a branch is asserted on the same cycle
      // as a fetch happens, the cache is being redirected at the end of the cycle, but the fetch
      // came out of the cache at the start of the cycle. This way, the scoreboard doesn't need to
      // do any re-ordering.
      @(posedge cfg.vif.clk);

      // "Output" transactions

      // Spot whether we've received some instruction data.
      //
      // Note that we ignore anything coming back when we have branch asserted. This can happen if
      // timing happens to work out that way or (more likely) the cycle after we've read an error,
      // when we can keep the ready line high but also assert branch, which means we will ignore
      // what comes back on this cycle.
      if (cfg.vif.ready & cfg.vif.valid & ~cfg.vif.branch) begin
        trans = ibex_icache_core_bus_item::type_id::create("trans");
        trans.trans_type = ICacheCoreBusTransTypeFetch;
        trans.address    = cfg.vif.addr;
        trans.insn_data  = cfg.vif.rdata;
        trans.err        = cfg.vif.err;
        trans.err_plus2  = cfg.vif.err_plus2;
        trans.enable     = 0;
        trans.busy       = 0;
        analysis_port.write(trans);

        if (cfg.en_cov) begin
          if (!$isunknown(last_addr)) cov.on_inc_fetches(last_addr, cfg.vif.addr);
          cov.fetch_cg.sample(cfg.vif.err, cfg.vif.err_plus2, cfg.vif.enable);
        end
        last_addr = cfg.vif.addr;
      end

      // Spot edges on the enable pin
      if (cfg.vif.enable != last_enable) begin
        trans = ibex_icache_core_bus_item::type_id::create("trans");
        trans.trans_type = ICacheCoreBusTransTypeEnable;
        trans.address    = 0;
        trans.insn_data  = 0;
        trans.err        = 0;
        trans.err_plus2  = 0;
        trans.enable     = cfg.vif.enable;
        trans.busy       = 0;
        analysis_port.write(trans);
      end
      last_enable = cfg.vif.enable;

      // Spot edges on the busy pin
      if (cfg.vif.busy != last_busy) begin
        trans = ibex_icache_core_bus_item::type_id::create("trans");
        trans.trans_type = ICacheCoreBusTransTypeBusy;
        trans.address    = 0;
        trans.insn_data  = 0;
        trans.err        = 0;
        trans.err_plus2  = 0;
        trans.enable     = 0;
        trans.busy       = cfg.vif.busy;
        analysis_port.write(trans);
      end
      last_busy = cfg.vif.busy;

      // "Input" transactions

      // Firstly, spot any branch event. There is no handshaking here: there is a branch event on
      // this cycle if the 'branch' signal is high.
      if (cfg.vif.branch) begin
        trans = ibex_icache_core_bus_item::type_id::create("trans");
        trans.trans_type = ICacheCoreBusTransTypeBranch;
        trans.address    = cfg.vif.branch_addr;
        trans.insn_data  = 0;
        trans.err        = 0;
        trans.err_plus2  = 0;
        trans.enable     = 0;
        trans.busy       = 0;
        analysis_port.write(trans);

        last_addr = 'x;
        if (cfg.en_cov) cov.branch_dest_cg.sample(cfg.vif.branch_addr);
      end

      // If coverage is enabled, spot when the branch spec line is high
      if (cfg.en_cov && cfg.vif.branch_spec) begin
        cov.branch_spec_cg.sample(cfg.vif.branch);
      end

      // Spot invalidate signals. These can last for several cycles, but we only care about the
      // first cycle, so we track the last value to spot posedges.
      if (cfg.vif.invalidate && !last_inval) begin
        trans = ibex_icache_core_bus_item::type_id::create("trans");
        trans.trans_type = ICacheCoreBusTransTypeInvalidate;
        trans.address    = 0;
        trans.insn_data  = 0;
        trans.err        = 0;
        trans.err_plus2  = 0;
        trans.enable     = 0;
        trans.busy       = 0;
        analysis_port.write(trans);
      end
      last_inval = cfg.vif.invalidate;
    end
  endtask

  protected task process_cancelled_valid();
    forever begin
      @(cfg.vif.cancelled_valid);
      cov.cancelled_valid_cg.sample(cfg.vif.ready);
    end
  endtask

endclass
