// Copyright lowRISC contributors (OpenTitan project).
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
    super.randomize_item(item);
    // If user-provided data is available, use it.
    if (cfg.has_h_user_data()) item.h_data = cfg.get_h_user_data();
  endfunction

  virtual task body();
    repeat (num_trans) begin : send_req
      `uvm_create(req)
      start_item(req);
      randomize_item(req);
      finish_item(req);
      get_response(rsp);
    end : send_req
  endtask

endclass
