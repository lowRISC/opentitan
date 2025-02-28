// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class reset_monitor extends dv_base_monitor #(
  .ITEM_T(reset_item),
  .CFG_T (reset_agent_cfg),
  .COV_T (reset_agent_cov)
);
  `uvm_component_utils(reset_monitor)

  uvm_analysis_port #(reset_item) reset_item_ap;
  uvm_analysis_port #(reset_state_e) reset_state_ap;

  // Standard SV/UVM methods
  extern function new(string name, uvm_component parent = null);

  // Parent methods
  extern protected task collect_trans();
endclass : reset_monitor


function reset_monitor::new(string name, uvm_component parent = null);
  super.new(name, parent);
  reset_item_ap = new("reset_item_ap", this);
  reset_state_ap = new("reset_state_ap", this);
endfunction : new

task reset_monitor::collect_trans();
  int cnt_assert_delay;
  int cnt_assert_width;
  reset_item tr;

  forever begin
    cnt_assert_delay  = 0;
    cnt_assert_width  = 0;

    // -------------------------
    // Reset assertion phase
    // -------------------------
    if (cfg.enable_debug_messages) begin
      `uvm_info(`gtn, "Wait reset assertion...", UVM_LOW)
    end
    fork
      begin : mon_assert_proc
        if (cfg.polarity == ActiveLow) begin
          @(negedge cfg.vif.rst_o);
        end else begin
          @(posedge cfg.vif.rst_o);
        end
      end
      begin : measure_delay_proc
        forever begin
          if (cfg.assert_is_sync) begin
            @(posedge cfg.vif.clk_i);
          end else begin
            #(1ps);
          end
          cnt_assert_delay++;
        end
      end
    join_any
    disable fork;

    if (cfg.enable_debug_messages) begin
      `uvm_info(`gtn, "Reset asserted", UVM_LOW)
    end

    // Broadcast to all the subscribers that a reset is ongoing
    reset_state_ap.write(ResetAsserted);

    // -------------------------
    // Reset deassertion phase
    // -------------------------
    if (cfg.enable_debug_messages) begin
      `uvm_info(`gtn, "Wait reset deassertion...", UVM_LOW)
    end
    fork
      begin : mon_deassert_proc
        if (cfg.polarity == ActiveLow) begin
          @(posedge cfg.vif.rst_o);
        end else begin
          @(negedge cfg.vif.rst_o);
        end
      end
      begin : measure_width_proc
        forever begin
          if (cfg.deassert_is_sync) begin
            @(posedge cfg.vif.clk_i);
          end else begin
            #(1ps);
          end
          cnt_assert_width++;
        end
      end
    join_any
    disable fork;

    if (cfg.enable_debug_messages) begin
      `uvm_info(`gtn, "Reset deasserted", UVM_LOW)
    end

    // Broadcast to all the subscribers that the reset is done
    reset_state_ap.write(ResetDeasserted);

    // Create the sequence item
    tr = reset_item::type_id::create("tr", this);
    tr.assert_delay = cnt_assert_delay;
    tr.assert_width = cnt_assert_width;

    if (cfg.enable_debug_messages) begin
      `uvm_info(`gtn, "Monitored transaction is:", UVM_LOW);
      tr.print();
    end

    // Broadcast the transaction to all the subscribers
    reset_item_ap.write(tr);
  end
endtask : collect_trans
