// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This interface allows injection of flash_ctrl fatal alert.

interface flash_ctrl_host_gnt_fault_if (
  input clk_i,
  input rst_ni
);
  `include "dv_macros.svh"
  `include "uvm_macros.svh"

  string msg_id = $sformatf("%m");
  string path = dv_utils_pkg::get_parent_hier($sformatf("%m"));
  string signal_forced = $sformatf("%s.muxed_part", path);

  class flash_ctrl_host_gnt_if_proxy extends sec_cm_pkg::sec_cm_base_if_proxy;
    `uvm_object_new

    // This injects the fault via force and releases it after a few cycles.
    virtual task automatic inject_fault();
      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_force(signal_forced, 1'b1))
      `uvm_info(msg_id, $sformatf("Injecting fault by forcing %0s high", signal_forced), UVM_MEDIUM)
      repeat (300) @(negedge clk_i);
      `DV_CHECK(uvm_hdl_release(signal_forced))
    endtask

    virtual task automatic restore_fault();
    endtask
  endclass

  flash_ctrl_host_gnt_if_proxy if_proxy;

  initial begin
    `DV_CHECK_FATAL(uvm_hdl_check_path(signal_forced), , msg_id)

    // Store the proxy object for TB to use
    if_proxy = new("if_proxy");
    // The sec_cm_type is bogus.
    if_proxy.sec_cm_type = sec_cm_pkg::SecCmPrimSparseFsmFlop;
    if_proxy.path = path;
    sec_cm_pkg::sec_cm_if_proxy_q.push_back(if_proxy);

    `uvm_info(msg_id, $sformatf("Interface proxy class is added for %s", path), UVM_HIGH)
  end
endinterface
