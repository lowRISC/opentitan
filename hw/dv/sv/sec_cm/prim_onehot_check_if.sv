// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Generic countermeasure interface for hardened onehot_check
//
// This contains a proxy class and store the object in sec_cm_pkg, which can be used in vseq to
// control inject_fault and restore_fault
interface prim_onehot_check_if #(
  parameter int unsigned AddrWidth   = 5,
  parameter int unsigned OneHotWidth = 2**AddrWidth,
  parameter bit          AddrCheck   = 1,
  parameter bit          EnableCheck = 1,
  parameter bit          StrictCheck = 1
) (
  input                          clk_i,
  input                          rst_ni,

  input  logic [OneHotWidth-1:0] oh_i,
  input  logic [AddrWidth-1:0]   addr_i,
  input  logic                   en_i);

  `include "dv_macros.svh"
  `include "uvm_macros.svh"
  import uvm_pkg::*;

  string msg_id = $sformatf("%m");

  string path = dv_utils_pkg::get_parent_hier($sformatf("%m"));
  string oh_signal_forced = $sformatf("%s.oh_i", path);
  string en_signal_forced = $sformatf("%s.en_i", path);

  // TODO, so far this parameter is always tie to 0 in design
  // Add more support when it's used
  `ASSERT_INIT(AddrCheckNotSupported, !AddrCheck)

  class prim_onehot_check_if_proxy extends sec_cm_pkg::sec_cm_base_if_proxy;
    `uvm_object_new

    logic[OneHotWidth-1:0] oh_orig_value;
    logic                  en_orig_value;

    virtual task inject_fault();
      logic[OneHotWidth-1:0] oh_force_value;
      logic                  en_force_value;

      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_read(oh_signal_forced, oh_orig_value))
      `DV_CHECK(uvm_hdl_read(en_signal_forced, en_orig_value))
      `DV_CHECK_STD_RANDOMIZE_FATAL(en_force_value)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(oh_force_value,
                                         if (StrictCheck) {
                                           if (en_force_value) $countones(oh_force_value) != 1;
                                           else                $countones(oh_force_value) != 0;
                                         } else if (!StrictCheck) {
                                           if (en_force_value) $countones(oh_force_value) > 1;
                                           else                $countones(oh_force_value) != 0;
                                         }
                                         // higher chance to test oh=0/1, when StrictCheck is set
                                         oh_force_value dist {
                                           0     :/ 1,
                                           1     :/ 1,
                                           [2:$] :/ 5};
                                         )

      `uvm_info(msg_id, $sformatf("Forcing %s from %0d to %0d",
                                  en_signal_forced, en_orig_value, en_force_value), UVM_LOW)
      `uvm_info(msg_id, $sformatf("Forcing %s from %0d to %0d",
                                  oh_signal_forced, oh_orig_value, oh_force_value), UVM_LOW)
      `DV_CHECK(uvm_hdl_force(en_signal_forced, en_force_value))
      `DV_CHECK(uvm_hdl_force(oh_signal_forced, oh_force_value))
      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_release(en_signal_forced))
      `DV_CHECK(uvm_hdl_release(oh_signal_forced))
    endtask

    virtual task restore_fault();
      `uvm_info(msg_id, $sformatf("Forcing %s original value %0d",
                                  en_signal_forced, en_orig_value), UVM_LOW)
      `uvm_info(msg_id, $sformatf("Forcing %s original value %0d",
                                  oh_signal_forced, oh_orig_value), UVM_LOW)
      `DV_CHECK(uvm_hdl_deposit(en_signal_forced, en_orig_value))
      `DV_CHECK(uvm_hdl_deposit(oh_signal_forced, oh_orig_value))
    endtask
  endclass

  prim_onehot_check_if_proxy if_proxy;

  initial begin
    `DV_CHECK_FATAL(uvm_hdl_check_path(en_signal_forced), , msg_id)
    `DV_CHECK_FATAL(uvm_hdl_check_path(oh_signal_forced), , msg_id)

    // Store the proxy object for TB to use
    if_proxy = new("if_proxy");
    if_proxy.sec_cm_type = sec_cm_pkg::SecCmPrimOnehot;
    if_proxy.path = path;
    sec_cm_pkg::sec_cm_if_proxy_q.push_back(if_proxy);

    `uvm_info(msg_id, $sformatf("Interface proxy class is added for %s", path), UVM_MEDIUM)
  end
endinterface
