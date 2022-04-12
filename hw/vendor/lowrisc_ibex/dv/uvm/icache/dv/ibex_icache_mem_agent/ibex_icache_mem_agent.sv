// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_mem_agent extends dv_base_agent #(
  .CFG_T          (ibex_icache_mem_agent_cfg),
  .DRIVER_T       (ibex_icache_mem_driver),
  .SEQUENCER_T    (ibex_icache_mem_sequencer),
  .MONITOR_T      (ibex_icache_mem_monitor),
  .COV_T          (ibex_icache_mem_agent_cov)
);

  `uvm_component_utils(ibex_icache_mem_agent)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get ibex_icache_mem_if handle
    if (!uvm_config_db#(virtual ibex_icache_mem_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get ibex_icache_mem_if handle from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.is_active) begin
      // Pass snooped requests from the monitor to the sequencer
      monitor.request_port.connect(sequencer.request_fifo.analysis_export);
    end
  endfunction

endclass
