// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Generic countermeasure interface for hardened counter
//
// This contains a proxy class and store the object in sec_cm_pkg, which can be used in vseq to
// control inject_fault and cleanup_fault
interface prim_count_if #(
  parameter int Width,
  parameter prim_count_pkg::prim_count_style_e CntStyle
) (
  input clk_i,
  input rst_ni,
  input err_o,
  input prim_alert_pkg::alert_tx_t alert_tx);

  localparam int ErrorToAlertMaxCycles = 5;

  string msg_id = $sformatf("%m.u_prim_count_if");

  prim_count_pkg::prim_count_style_e cnt_style = CntStyle;

  string cnt_hier_path;

  class prim_count_if_proxy extends sec_cm_pkg::sec_cm_base_if_proxy;
    `uvm_object_new

    logic[Width-1:0] orig_value;

    virtual task inject_fault();
      logic[Width-1:0] force_value;

      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_read(cnt_hier_path, orig_value))
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(force_value, force_value != orig_value;)
      uvm_hdl_deposit(cnt_hier_path, force_value);
      `uvm_info(msg_id, $sformatf("Forcing %s from %0d to %0d",
                                cnt_hier_path, orig_value, force_value), UVM_LOW)

      @(posedge clk_i);
    endtask

    virtual task cleanup_fault();
      uvm_hdl_deposit(cnt_hier_path, orig_value);
      `uvm_info(msg_id, $sformatf("Forcing %s to original value %0d", cnt_hier_path, orig_value),
                UVM_LOW)
    endtask
  endclass

  prim_count_if_proxy if_proxy;

  initial begin
    string prim_path = dv_utils_pkg::get_parent_hier($sformatf("%m"));
    case (cnt_style)
      prim_count_pkg::CrossCnt: cnt_hier_path = $sformatf("%s.up_cnt_q", prim_path);
      prim_count_pkg::DupCnt: cnt_hier_path = $sformatf("%s.up_cnt_q[0]", prim_path);
      default: `uvm_fatal(msg_id, $sformatf("unsupported style %s", cnt_style.name()))
    endcase


    // Store the proxy object for TB to use
    if_proxy = new("if_proxy");
    if_proxy.sec_cm_type = sec_cm_pkg::SecCmPrimCount;
    if_proxy.prim_path = prim_path;
    sec_cm_pkg::sec_cm_if_proxy_q.push_back(if_proxy);

    `uvm_info(msg_id, $sformatf("Interface proxy class is added for %s", prim_path), UVM_MEDIUM)
  end

  `ASSERT(ErrorTriggerAlert, $rose(err_o) |->
                             ##[1:ErrorToAlertMaxCycles] $rose(alert_tx.alert_p));
endinterface
