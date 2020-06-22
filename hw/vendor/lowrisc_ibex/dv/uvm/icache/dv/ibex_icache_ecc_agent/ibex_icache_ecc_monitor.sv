// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_ecc_monitor extends dv_base_monitor #(
    .ITEM_T (ibex_icache_ecc_bus_item),
    .CFG_T  (ibex_icache_ecc_agent_cfg)
  );
  `uvm_component_utils(ibex_icache_ecc_monitor)

  // the base class provides the following handles for use:
  // ibex_icache_ecc_agent_cfg: cfg
  // ibex_icache_ecc_agent_cov: cov
  // uvm_analysis_port #(ibex_icache_ecc_bus_item): analysis_port

  `uvm_component_new

  // collect transactions forever - already forked in dv_base_moditor::run_phase
  virtual protected task collect_trans(uvm_phase phase);
    ibex_icache_ecc_bus_item trans;
    forever begin
      cfg.vif.wait_read();
      // If this isn't a reset pulse, we have a read transaction. Report it.
      if (!cfg.vif.rst_n) begin
        trans = ibex_icache_ecc_bus_item::type_id::create("trans");
        trans.addr         = cfg.vif.last_addr;
        trans.bad_bit_mask = cfg.vif.bad_bit_mask;
        trans.sram_rdata   = cfg.vif.rdata;
        analysis_port.write(trans);
      end
      @(posedge cfg.vif.clk_i);
    end
  endtask

endclass
