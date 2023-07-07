// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Generic countermeasure interface for double LFSR
//
// This contains a proxy class and store the object in sec_cm_pkg, which can be used in vseq to
// control inject_fault and restore_fault
interface prim_double_lfsr_if #(
  parameter int Width = 2
) (
  input clk_i,
  input rst_ni
);

  `include "dv_macros.svh"
  `include "uvm_macros.svh"
  import uvm_pkg::*;

  string msg_id = $sformatf("%m");

  string path = dv_utils_pkg::get_parent_hier($sformatf("%m"));
  string signal_forced = $sformatf("%s.lfsr_state[0]", path);
  string signal_for_restore = $sformatf("%s.lfsr_state[1]", path);

  class prim_double_lfsr_if_proxy extends sec_cm_pkg::sec_cm_base_if_proxy;
    `uvm_object_new

    logic [Width-1:0] orig_value;

    virtual task automatic inject_fault();
      logic [Width-1:0] force_value;

      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_read(signal_forced, orig_value))
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(force_value, force_value != orig_value;)

      `DV_CHECK(uvm_hdl_force(signal_forced, force_value))
      `uvm_info(msg_id, $sformatf(
                "Forcing %s from %0d to %0d", signal_forced, orig_value, force_value), UVM_LOW)

      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_release(signal_forced))
    endtask

    virtual task automatic restore_fault();
      logic [Width-1:0] restore_value;
      `DV_CHECK(uvm_hdl_read(signal_for_restore, restore_value))
      `DV_CHECK(uvm_hdl_deposit(signal_forced, restore_value))
      `uvm_info(msg_id, $sformatf("Forcing %s to matching value %0d", signal_forced, restore_value),
                UVM_LOW)
    endtask
  endclass

  prim_double_lfsr_if_proxy if_proxy;

  initial begin
    `DV_CHECK_FATAL(uvm_hdl_check_path(signal_forced),, msg_id)
    `DV_CHECK_FATAL(uvm_hdl_check_path(signal_for_restore),, msg_id)

    // Store the proxy object for TB to use
    if_proxy = new("if_proxy");
    if_proxy.sec_cm_type = sec_cm_pkg::SecCmPrimDoubleLfsr;
    if_proxy.path = path;
    sec_cm_pkg::sec_cm_if_proxy_q.push_back(if_proxy);

    `uvm_info(msg_id, $sformatf("Interface proxy class is added for %s", path), UVM_HIGH)
  end
endinterface
