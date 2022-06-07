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

  typedef enum bit [1:0] {
    OnehotFault,
    OnehotEnableFault,
    OnehotAddrFault
  } onehot_fault_type_e;

  string msg_id = $sformatf("%m");

  string path = dv_utils_pkg::get_parent_hier($sformatf("%m"));
  string oh_signal_forced = $sformatf("%s.oh_i", path);
  string en_signal_forced = $sformatf("%s.en_i", path);
  string addr_signal_forced = $sformatf("%s.addr_i", path);

  class prim_onehot_check_if_proxy extends sec_cm_pkg::sec_cm_base_if_proxy;
    `uvm_object_new

    logic[OneHotWidth-1:0] oh_orig_value;
    logic[AddrWidth-1:0]   addr_orig_value;
    logic                  en_orig_value;

    virtual task inject_fault();
      onehot_fault_type_e  onehot_fault_type;
      bit[OneHotWidth-1:0] oh_force_value;
      bit[AddrWidth-1:0]   addr_force_value;
      bit                  en_force_value;
      bit                  success;

      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_read(oh_signal_forced, oh_orig_value))
      `DV_CHECK(uvm_hdl_read(en_signal_forced, en_orig_value))
      `DV_CHECK(uvm_hdl_read(addr_signal_forced, addr_orig_value))
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(onehot_fault_type,
                                         AddrWidth == 1 -> onehot_fault_type != OnehotFault;
                                         !AddrCheck -> onehot_fault_type != OnehotAddrFault;
                                         !EnableCheck -> onehot_fault_type != OnehotEnableFault;
                                         )

      // TODO, add covergroup for onehot_fault_type
      case (onehot_fault_type)
        OnehotFault: begin
          success = std::randomize(en_force_value, oh_force_value, addr_force_value) with {
              !$onehot0(oh_force_value);
              AddrCheck -> oh_force_value[addr_force_value] == (|oh_force_value);
            };
        end
        OnehotEnableFault: begin
          success = std::randomize(en_force_value, oh_force_value, addr_force_value) with {
              $onehot0(oh_force_value);
              AddrCheck -> oh_force_value[addr_force_value] == (|oh_force_value);
              if (StrictCheck) {
                (|oh_force_value) != en_force_value;
              } else {
                !en_force_value && (|oh_force_value);
              }
            };
        end
        OnehotAddrFault: begin
          success = std::randomize(en_force_value, oh_force_value, addr_force_value) with {
              $onehot0(oh_force_value);
              oh_force_value[addr_force_value] != (|oh_force_value);
            };
        end
        default: `uvm_fatal(msg_id, $sformatf("Unexpected onehot_fault_type: %s",
                                              onehot_fault_type.name))
      endcase
      `uvm_info(msg_id, $sformatf("onehot_fault_type: %0s", onehot_fault_type.name), UVM_LOW)
      `DV_CHECK_FATAL(success)

      `uvm_info(msg_id, $sformatf("Forcing %s from %0d to %0d",
                                  en_signal_forced, en_orig_value, en_force_value), UVM_LOW)
      `uvm_info(msg_id, $sformatf("Forcing %s from %0d to %0d",
                                  oh_signal_forced, oh_orig_value, oh_force_value), UVM_LOW)
      `uvm_info(msg_id, $sformatf("Forcing %s from %0d to %0d",
                                  addr_signal_forced, addr_orig_value, addr_force_value), UVM_LOW)

      `DV_CHECK(uvm_hdl_force(en_signal_forced, en_force_value))
      `DV_CHECK(uvm_hdl_force(oh_signal_forced, oh_force_value))
      `DV_CHECK(uvm_hdl_force(addr_signal_forced, addr_force_value))
      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_release(en_signal_forced))
      `DV_CHECK(uvm_hdl_release(oh_signal_forced))
      `DV_CHECK(uvm_hdl_release(addr_signal_forced))
    endtask

    virtual task restore_fault();
      `uvm_info(msg_id, $sformatf("Forcing %s original value %0d",
                                  en_signal_forced, en_orig_value), UVM_LOW)
      `uvm_info(msg_id, $sformatf("Forcing %s original value %0d",
                                  oh_signal_forced, oh_orig_value), UVM_LOW)
      `uvm_info(msg_id, $sformatf("Forcing %s original value %0d",
                                  addr_signal_forced, addr_orig_value), UVM_LOW)
      `DV_CHECK(uvm_hdl_deposit(en_signal_forced, en_orig_value))
      `DV_CHECK(uvm_hdl_deposit(oh_signal_forced, oh_orig_value))
      `DV_CHECK(uvm_hdl_deposit(addr_signal_forced, addr_orig_value))
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
