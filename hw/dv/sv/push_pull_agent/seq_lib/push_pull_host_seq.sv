// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Request sequence for Push and Pull protocols.
// This sequence will send num_trans requests to the DUT.

class push_pull_host_seq #(parameter int HostDataWidth = 32,
                           parameter int DeviceDataWidth = HostDataWidth)
  extends push_pull_base_seq #(HostDataWidth, DeviceDataWidth);

  `uvm_object_param_utils(push_pull_host_seq#(HostDataWidth, DeviceDataWidth))

  `uvm_object_new

  // Default to send 1 transactions.
  // Can be overridden at a higher layer.
  int unsigned num_trans = 1;

  // Randomizes the host req.
  virtual function void randomize_item(push_pull_item #(HostDataWidth, DeviceDataWidth) item);
      `uvm_info(`gfn, $sformatf("item passed: %0s", item.convert2string()), UVM_HIGH)
    super.randomize_item(item);
      `uvm_info(`gfn, $sformatf("item randomized: %0s", item.convert2string()), UVM_HIGH)
    // If user-provided data is available, use it.
    if (cfg.has_h_user_data()) item.h_data = cfg.get_h_user_data();
      `uvm_info(`gfn, $sformatf("item done: %0s", item.convert2string()), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("user data = %0d", item.h_data), UVM_LOW)
  endfunction

  virtual task body();
    repeat (num_trans) begin : send_req
      `uvm_create(req)
      `uvm_info(`gfn, $sformatf("request created: %0s", req.convert2string()), UVM_HIGH)
      start_item(req);
      `uvm_info(`gfn, $sformatf("item starte: %0s", req.convert2string()), UVM_HIGH)
      randomize_item(req);
      `uvm_info(`gfn, $sformatf("Starting sequence item: %0s", req.convert2string()), UVM_HIGH)
      finish_item(req);
      get_response(rsp);
      `uvm_info(`gfn, $sformatf("Received response: %0s", rsp.convert2string()), UVM_HIGH)
    end : send_req
  endtask

endclass
