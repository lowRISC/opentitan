// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_ifetch_monitor extends uvm_monitor;
  protected virtual core_ibex_ifetch_if vif;

  uvm_analysis_port#(ibex_ifetch_seq_item) item_collected_port;

  `uvm_component_utils(ibex_ifetch_monitor)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    item_collected_port = new("item_collected_port", this);

    if(!uvm_config_db#(virtual core_ibex_ifetch_if)::get(this, "", "ifetch_if", vif)) begin
      `uvm_fatal("NOVIF", {"virtual interface must be set for: ", get_full_name(), ".vif"});
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    ibex_ifetch_seq_item trans_collected;

    wait (vif.monitor_cb.reset === 1'b0);

    forever begin
      while(!(vif.monitor_cb.fetch_valid && vif.monitor_cb.fetch_ready)) vif.wait_clks(1);

      trans_collected                 = ibex_ifetch_seq_item::type_id::create("trans_collected");
      trans_collected.fetch_rdata     = vif.monitor_cb.fetch_rdata;
      trans_collected.fetch_addr      = vif.monitor_cb.fetch_addr;
      trans_collected.fetch_err       = vif.monitor_cb.fetch_err;
      trans_collected.fetch_err_plus2 = vif.monitor_cb.fetch_err_plus2;

      `uvm_info(`gfn, $sformatf("Seen ifetch:\n%s", trans_collected.sprint()),
        UVM_HIGH)

      item_collected_port.write(trans_collected);

      vif.wait_clks(1);
    end
  endtask: run_phase
endclass : ibex_ifetch_monitor
