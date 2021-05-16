// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_trace_monitor extends dv_base_monitor #(
    .ITEM_T (otbn_trace_item),
    .CFG_T (otbn_env_cfg),
    .COV_T (otbn_env_cov)
  );

  `uvm_component_utils(otbn_trace_monitor)
  `uvm_component_new

  protected task collect_trans(uvm_phase phase);
    otbn_trace_item item;
    forever begin
      @(posedge cfg.trace_vif.clk_i);
      if (cfg.trace_vif.rst_ni === 1'b1) begin
        if (cfg.trace_vif.insn_valid && !cfg.trace_vif.insn_stall) begin
          item = otbn_trace_item::type_id::create("item");
          item.insn_addr = cfg.trace_vif.insn_addr;
          analysis_port.write(item);
        end
      end
    end
  endtask

endclass
