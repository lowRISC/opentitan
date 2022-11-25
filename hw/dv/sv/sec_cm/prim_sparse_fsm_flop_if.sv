// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Generic countermeasure interface for hardened FSM
//
// This contains a proxy class and store the object in sec_cm_pkg, which can be used in vseq to
// control inject_fault and restore_fault
//

interface prim_sparse_fsm_flop_if #(
  parameter int Width = 2,
  parameter string CustomForceName = ""
) (
  input clk_i,
  input rst_ni);

  `include "dv_macros.svh"
  `include "uvm_macros.svh"
  import uvm_pkg::*;

  localparam int MaxFlipBits = 2;

  string msg_id = $sformatf("%m");

  string path = dv_utils_pkg::get_parent_hier($sformatf("%m"));
  string signal_forced = $sformatf("%s.u_state_flop.q_o", path);

  // This signal only has to be forced if the associated parameter
  // CustomForceName in prim_sparse_fsm_flop is set to a non-empty string.
  string parent_path = dv_utils_pkg::get_parent_hier($sformatf("%m"), 2);
  string custom_signal_forced = $sformatf("%s.%s", parent_path, CustomForceName);

  class prim_sparse_fsm_flop_if_proxy extends sec_cm_pkg::sec_cm_base_if_proxy;
    `uvm_object_new

    logic[Width-1:0] orig_value;

    virtual task automatic inject_fault(output bit success);
      logic[Width-1:0] force_value;
      uvm_queue#(bit[Width-1:0]) state_values;

      if (uvm_config_db#(uvm_queue#(bit[Width-1:0]))::get(null, path, "state_values", state_values)
          &&
          state_values.size()) begin
        int value_to_wait_for_index;
        int value_to_wait_for;
        int cycles_wait;
        bit found_value;
        int state_wait_timeout = 3000;

        uvm_config_db#(int)::get(null, path, "state_wait_timeout", state_wait_timeout);

        found_value = 1'b0;
        cycles_wait = 0;

        value_to_wait_for_index = $urandom_range(0, state_values.size() - 1);
        value_to_wait_for = state_values.get(value_to_wait_for_index);

        while (!found_value) begin
          @(negedge clk_i);
          `DV_CHECK(uvm_hdl_read(signal_forced, orig_value))

          if (orig_value == value_to_wait_for) begin
            found_value = 1;
          end else begin
            cycles_wait++;

            if (cycles_wait == state_wait_timeout) begin
              `uvm_info(msg_id, $sformatf("Timed out waiting for FSM state %x", value_to_wait_for),
                        UVM_LOW);

              success = 0;
              return;
            end
          end
        end
      end else begin
        @(negedge clk_i);
        `DV_CHECK(uvm_hdl_read(signal_forced, orig_value))
      end

      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(force_value,
          $countones(force_value ^ orig_value) inside {[1: MaxFlipBits]};)

      `uvm_info(msg_id, $sformatf("Forcing %s from %0d to %0d",
                                  signal_forced, orig_value, force_value), UVM_LOW)
      `DV_CHECK(uvm_hdl_force(signal_forced, force_value))
      if (CustomForceName != "") begin
        `uvm_info(msg_id, $sformatf("Forcing %s from %0d to %0d",
                                    custom_signal_forced, orig_value, force_value), UVM_LOW)
        `DV_CHECK(uvm_hdl_deposit(custom_signal_forced, force_value))
      end
      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_release(signal_forced))

      success = 1;
    endtask

    virtual task automatic restore_fault();
      // Don't invoke restore_fault if CustomForceName is set, so as to avoid some complication,
      // becasue restore_fault may cause misaligment on signal_forced and custom_signal_forced
      // signal_forced is net, while custom_signal_forced is a flop.
      // For example, if the state_d stays at error_state, we restore the net (signal_forced) and
      // the flop (custom_signal_forced) to an idle_state. signal_forced won't be changed to
      // idle_state as state_d has no change, while custom_signal_forced will become idile_state as
      // it's updated in every cycle.
      // Another approach is to deposit the value in the flop but we will have different
      // implementation in the prim and the path is different in the close source
      if (CustomForceName != "") return;

      `uvm_info(msg_id, $sformatf("Forcing %s to original value %0d", signal_forced, orig_value),
                UVM_LOW)
      `DV_CHECK(uvm_hdl_deposit(signal_forced, orig_value))
      `uvm_info(msg_id, $sformatf("Forcing %s to original value %0d", custom_signal_forced,
                orig_value), UVM_LOW)
      `DV_CHECK(uvm_hdl_deposit(custom_signal_forced, orig_value))
    endtask
  endclass

  prim_sparse_fsm_flop_if_proxy if_proxy;

  initial begin
    `DV_CHECK_FATAL(uvm_hdl_check_path(signal_forced), , msg_id)

    // Store the proxy object for TB to use
    if_proxy = new("if_proxy");
    if_proxy.sec_cm_type = sec_cm_pkg::SecCmPrimSparseFsmFlop;
    if_proxy.path = path;
    sec_cm_pkg::sec_cm_if_proxy_q.push_back(if_proxy);

    `uvm_info(msg_id, $sformatf("Interface proxy class is added for %s", path), UVM_MEDIUM)
  end

endinterface

