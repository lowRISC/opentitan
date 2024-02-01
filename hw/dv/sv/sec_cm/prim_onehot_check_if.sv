// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Generic countermeasure interface for hardened onehot_check
//
// This contains a proxy class and store the object in sec_cm_pkg, which can be used in vseq to
// control inject_fault and restore_fault.
//
// This interface is parameterized, and the AddrCheck parameter can be 0 or 1 in some instances.
// For the instances with AddrCheck == 0 we end up with a coverage hole, so in order to
// avoid this there are two derived classes from prim_onehot_check_if_proxy that differ
// in their embedded covergroups.

interface prim_onehot_check_if #(
  parameter int unsigned AddrWidth   = 5,
  parameter int unsigned OneHotWidth = 2 ** AddrWidth,
  parameter bit          AddrCheck   = 1,
  parameter bit          EnableCheck = 1,
  parameter bit          StrictCheck = 1
) (
  input clk_i,
  input rst_ni,

  input logic [OneHotWidth-1:0] oh_i,
  input logic [  AddrWidth-1:0] addr_i,
  input logic                   en_i
);

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
    logic [OneHotWidth-1:0] oh_orig_value;
    logic [AddrWidth-1:0]   addr_orig_value;
    logic                   en_orig_value;

    function new(string name = "");
      super.new(name);
    endfunction : new

    virtual function void sample_cov(onehot_fault_type_e onehot_fault_type);
      `uvm_fatal(msg_id, "sample_cov in base class")
    endfunction

    virtual task inject_fault();
      onehot_fault_type_e                   onehot_fault_type;
      bit                 [OneHotWidth-1:0] oh_force_value;
      bit                 [  AddrWidth-1:0] addr_force_value;
      bit                                   en_force_value;
      bit                                   success;

      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_read(oh_signal_forced, oh_orig_value))
      `DV_CHECK(uvm_hdl_read(en_signal_forced, en_orig_value))
      `DV_CHECK(uvm_hdl_read(addr_signal_forced, addr_orig_value))
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(onehot_fault_type,
                                         AddrWidth == 1 -> onehot_fault_type != OnehotFault;
                                         !AddrCheck -> onehot_fault_type != OnehotAddrFault;
                                         !EnableCheck -> onehot_fault_type != OnehotEnableFault;)

      if (sec_cm_pkg::en_sec_cm_cov) sample_cov(onehot_fault_type);
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
        default:
        `uvm_fatal(msg_id, $sformatf("Unexpected onehot_fault_type: %s", onehot_fault_type.name))
      endcase
      `uvm_info(msg_id, $sformatf("onehot_fault_type: %0s", onehot_fault_type.name), UVM_LOW)
      `DV_CHECK_FATAL(success)

      `uvm_info(msg_id, $sformatf(
                "Forcing %s from %0d to %0d", en_signal_forced, en_orig_value, en_force_value),
                UVM_LOW)
      `uvm_info(msg_id, $sformatf(
                "Forcing %s from %0d to %0d", oh_signal_forced, oh_orig_value, oh_force_value),
                UVM_LOW)
      `uvm_info(msg_id, $sformatf(
                "Forcing %s from %0d to %0d", addr_signal_forced, addr_orig_value, addr_force_value
                ), UVM_LOW)

      `DV_CHECK(uvm_hdl_force(en_signal_forced, en_force_value))
      `DV_CHECK(uvm_hdl_force(oh_signal_forced, oh_force_value))
      `DV_CHECK(uvm_hdl_force(addr_signal_forced, addr_force_value))
      @(negedge clk_i);
      `DV_CHECK(uvm_hdl_release(en_signal_forced))
      `DV_CHECK(uvm_hdl_release(oh_signal_forced))
      `DV_CHECK(uvm_hdl_release(addr_signal_forced))
    endtask

    virtual task restore_fault();
      `uvm_info(msg_id, $sformatf("Forcing %s original value %0d", en_signal_forced, en_orig_value),
                UVM_LOW)
      `uvm_info(msg_id, $sformatf("Forcing %s original value %0d", oh_signal_forced, oh_orig_value),
                UVM_LOW)
      `uvm_info(msg_id, $sformatf("Forcing %s original value %0d",
                                  addr_signal_forced, addr_orig_value), UVM_LOW)
      `DV_CHECK(uvm_hdl_deposit(en_signal_forced, en_orig_value))
      `DV_CHECK(uvm_hdl_deposit(oh_signal_forced, oh_orig_value))
      `DV_CHECK(uvm_hdl_deposit(addr_signal_forced, addr_orig_value))
    endtask
  endclass : prim_onehot_check_if_proxy

  class prim_onehot_check_with_addr_fault_if_proxy extends prim_onehot_check_if_proxy;

    covergroup onehot_with_addr_fault_cg (string name) with function sample(
          onehot_fault_type_e onehot_fault_type);
      option.name = name;
      option.per_instance = 1;

      cp_onehot_fault: coverpoint onehot_fault_type {
        option.weight = AddrWidth > 1;  // set to 0 to disable it if it's not supported
        bins hit = {OnehotFault};
      }
      cp_onehot_enable_fault: coverpoint onehot_fault_type {
        option.weight = EnableCheck;  // set to 0 to disable it if it's not supported
        bins hit = {OnehotEnableFault};
      }
      cp_onehot_addr_fault: coverpoint onehot_fault_type {
        option.weight = AddrCheck;  // set to 0 to disable it if it's not supported
        bins hit = {OnehotAddrFault};
      }
    endgroup

    virtual function void sample_cov(onehot_fault_type_e onehot_fault_type);
      onehot_with_addr_fault_cg.sample(onehot_fault_type);
    endfunction

    function new(string name = "");
      super.new(name);
      if (sec_cm_pkg::en_sec_cm_cov) begin
        onehot_with_addr_fault_cg = new(msg_id);
      end
    endfunction
  endclass : prim_onehot_check_with_addr_fault_if_proxy

  class prim_onehot_check_without_addr_fault_if_proxy extends prim_onehot_check_if_proxy;

    covergroup onehot_without_addr_fault_cg (string name) with function sample(
          onehot_fault_type_e onehot_fault_type);
      option.name = name;
      option.per_instance = 1;

      cp_onehot_fault: coverpoint onehot_fault_type {
        option.weight = AddrWidth > 1;  // set to 0 to disable it if it's not supported
        bins hit = {OnehotFault};
      }
      cp_onehot_enable_fault: coverpoint onehot_fault_type {
        option.weight = EnableCheck;  // set to 0 to disable it if it's not supported
        bins hit = {OnehotEnableFault};
      }
    endgroup

    virtual function void sample_cov(onehot_fault_type_e onehot_fault_type);
      `DV_CHECK_NE(onehot_fault_type, OnehotAddrFault)
      onehot_without_addr_fault_cg.sample(onehot_fault_type);
    endfunction

    function new(string name = "");
      super.new(name);
      if (sec_cm_pkg::en_sec_cm_cov) begin
        onehot_without_addr_fault_cg = new(msg_id);
      end
    endfunction
  endclass : prim_onehot_check_without_addr_fault_if_proxy

  prim_onehot_check_if_proxy if_proxy;

  initial begin
    `DV_CHECK_FATAL(uvm_hdl_check_path(en_signal_forced),, msg_id)
    `DV_CHECK_FATAL(uvm_hdl_check_path(oh_signal_forced),, msg_id)

    // Store the proxy object for TB to use
    if (AddrCheck) begin
      prim_onehot_check_with_addr_fault_if_proxy with_addr_fault_if_proxy;
      with_addr_fault_if_proxy = new("if_proxy");
      if_proxy = with_addr_fault_if_proxy;
    end else begin
      prim_onehot_check_without_addr_fault_if_proxy without_addr_fault_if_proxy;
      without_addr_fault_if_proxy = new("if_proxy");
      if_proxy = without_addr_fault_if_proxy;
    end
    if_proxy.sec_cm_type = sec_cm_pkg::SecCmPrimOnehot;
    if_proxy.path = path;
    sec_cm_pkg::sec_cm_if_proxy_q.push_back(if_proxy);

    `uvm_info(msg_id, $sformatf("Interface proxy class is added for %s", path), UVM_HIGH)
  end
endinterface
