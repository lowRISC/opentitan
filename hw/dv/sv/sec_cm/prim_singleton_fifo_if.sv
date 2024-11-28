// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Countermeasure interface for the hardened 1-bit counter in prim_fifo_sync if Depth=1.
//
// This interface can be bound into a prim_fifo_sync instance. Many instances of the interface will
// not do anything, because Depth > 1 or or Secure = 0. However if Depth = 1 and Secure = 1, the
// nested prim_singleton_fifo_if_proxy class will register the instance in sec_cm_pkg and can
// inject/restore faults.
interface prim_singleton_fifo_if #(
  parameter int Depth = 1,
  parameter bit Secure = 1'b1
) (
  input clk_i,
  input rst_ni
);

  `include "dv_macros.svh"
  `include "uvm_macros.svh"
  import uvm_pkg::*;

  string msg_id = $sformatf("%m");

  string path = dv_utils_pkg::get_parent_hier($sformatf("%m"));
  string signal_forced;

  class prim_singleton_fifo_if_proxy extends sec_cm_pkg::sec_cm_base_if_proxy;
    logic orig_value;

    function new(string name="");
      super.new(name);
    endfunction

    virtual task automatic inject_fault();
      logic force_value;

      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_read(signal_forced, orig_value))
      `DV_CHECK(uvm_hdl_force(signal_forced, ~orig_value))
      `uvm_info(msg_id,
                $sformatf("Forcing %s from %0d to %0d", signal_forced, orig_value, ~orig_value),
                UVM_LOW)

      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_release(signal_forced))
    endtask

    virtual task automatic restore_fault();
      `DV_CHECK(uvm_hdl_deposit(signal_forced, orig_value))
      `uvm_info(msg_id, $sformatf("Forcing %s to original value %0d", signal_forced, orig_value),
                UVM_LOW)
    endtask
  endclass

  if (Depth == 1 && Secure) begin : gen_secure_singleton
    prim_singleton_fifo_if_proxy if_proxy;
    initial begin
      string local_signal;
      local_signal = $urandom_range(0, 1) ? "inv_full" : "full_q";
      signal_forced = $sformatf("%s.%s", path, local_signal);
      `DV_CHECK_FATAL(uvm_hdl_check_path(signal_forced),, msg_id)

      // Store the proxy object for TB to use
      if_proxy = new("if_proxy");
      if_proxy.sec_cm_type = sec_cm_pkg::SecCmSingletonFifo;
      if_proxy.path = path;
      sec_cm_pkg::sec_cm_if_proxy_q.push_back(if_proxy);

      `uvm_info(msg_id, $sformatf("Interface proxy class is added for %s", path), UVM_HIGH)
    end
  end

endinterface
