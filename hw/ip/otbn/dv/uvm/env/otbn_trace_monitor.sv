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

    // The trace monitor is only used for coverage collection; disable it if coverage is not
    // enabled.
    if (!cfg.en_cov) begin
      return;
    end

    forever begin
      @(posedge cfg.trace_vif.clk_i);
      if (cfg.trace_vif.rst_ni === 1'b1) begin
        if (cfg.trace_vif.insn_valid && !cfg.trace_vif.insn_stall) begin
          // Belt-and-braces check to make sure that the trace_vif and loop_vif are talking about
          // the same instruction.
          `DV_CHECK_EQ_FATAL(cfg.trace_vif.insn_addr, cfg.loop_vif.insn_addr)

          item = otbn_trace_item::type_id::create("item");
          item.insn_addr = cfg.trace_vif.insn_addr;
          item.insn_data = cfg.trace_vif.insn_data;
          item.gpr_operand_a = cfg.trace_vif.rf_base_rd_data_a;
          item.gpr_operand_b = cfg.trace_vif.rf_base_rd_data_b;
          item.wdr_operand_a = cfg.trace_vif.rf_bignum_rd_data_a;
          item.wdr_operand_b = cfg.trace_vif.rf_bignum_rd_data_b;
          item.flags_write_data = cfg.trace_vif.flags_write_data;
          item.gpr_write_data = cfg.trace_vif.rf_base_wr_data;
          item.at_current_loop_end_insn = cfg.loop_vif.at_current_loop_end_insn;

          `uvm_info(`gfn, $sformatf("saw trace item:\n%0s", item.sprint()), UVM_HIGH)
          analysis_port.write(item);
        end
      end
    end
  endtask

endclass
