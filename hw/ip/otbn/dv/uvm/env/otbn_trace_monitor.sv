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
    bit             item_valid = 1'b0;

    // The trace monitor is only used for coverage collection; disable it if coverage is not
    // enabled.
    if (!cfg.en_cov) begin
      return;
    end

    forever begin
      @(posedge cfg.trace_vif.clk_i);

      if (cfg.trace_vif.rst_ni !== 1'b1) begin
        item_valid = 1'b0;
      end else begin
        if (cfg.trace_vif.insn_valid) begin
          if (!item_valid) begin
            // This is the first cycle of a (possibly multi-cycle) instruction. Sample everything
            // now because things might change in the interim, but don't write anything to the
            // analysis port until the instruction is not stalled.

            // A belt-and-braces check to make sure that the trace_vif and loop_vif are talking
            // about the same instruction.
            `DV_CHECK_EQ_FATAL(cfg.trace_vif.insn_addr, cfg.loop_vif.insn_addr_i)

            item = otbn_trace_item::type_id::create("item");
            item.insn_addr = cfg.trace_vif.insn_addr;
            item.insn_data = cfg.trace_vif.insn_data;
            item.gpr_operand_a = cfg.trace_vif.rf_base_rd_data_a;
            item.gpr_operand_b = cfg.trace_vif.rf_base_rd_data_b;
            item.wdr_operand_a = cfg.trace_vif.rf_bignum_rd_data_a;
            item.wdr_operand_b = cfg.trace_vif.rf_bignum_rd_data_b;
            item.flags_read_data = cfg.trace_vif.flags_read_data;
            item.flags_write_valid = cfg.trace_vif.flags_write;
            item.flags_write_data = cfg.trace_vif.flags_write_data;
            item.gpr_write_data = cfg.trace_vif.rf_base_wr_data;
            item.wdr_write_data = cfg.trace_vif.rf_bignum_wr_data;
            item.call_stack_flags = cfg.rf_base_vif.get_call_stack_flags();
            item.loop_stack_fullness = cfg.loop_vif.get_fullness();
            item.call_stack_fullness = cfg.rf_base_vif.get_call_stack_fullness();
            item.has_sideload_key = cfg.keymgr_sideload_agent_cfg.vif.sideload_key.valid;
            item.current_loop_end = cfg.loop_vif.current_loop_end;
            item.at_current_loop_end_insn = cfg.loop_vif.at_current_loop_end_insn;
            for (int unsigned i_word = 0; i_word < BaseWordsPerWLEN; i_word++) begin
              item.mod[i_word*32+:32] = cfg.alu_bignum_vif.mod_intg_q[i_word*39+:32];
            end
            item.new_acc_extended = cfg.mac_bignum_vif.get_sum_value();

            item_valid = 1'b1;
          end
          if (!cfg.trace_vif.insn_stall) begin
            // This is the last cycle of a (possibly multi-cycle) instruction. We sampled the item
            // on the first cycle. Push it to the analysis port now.
            `DV_CHECK_FATAL(item_valid, "no valid trace item?!")

            `uvm_info(`gfn, $sformatf("saw trace item:\n%0s", item.sprint()), UVM_HIGH)
            analysis_port.write(item);

            item_valid = 1'b0;
          end
        end
      end
    end
  endtask
endclass
