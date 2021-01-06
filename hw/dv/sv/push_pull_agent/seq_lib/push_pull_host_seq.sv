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

  virtual task body();
    for (int i = 0; i < num_trans; i++) begin : send_req
      req = push_pull_item#(HostDataWidth, DeviceDataWidth)::type_id::create(
        $sformatf("req[%0d]", i));
      start_item(req);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        if (cfg.zero_delays) {
          host_delay == 0;
        } else {
          host_delay inside {[cfg.host_delay_min : cfg.host_delay_max]};
        }
      )
      // If user-provided data is ready, use this instead of random data.
      if (cfg.has_h_user_data()) req.h_data = cfg.get_h_user_data();
      `uvm_info(`gfn, $sformatf("Starting sequence item: %0s", req.convert2string()), UVM_HIGH)
      // We don't care about response data here, the monitor will log all complete transactions.
      finish_item(req);
      get_response(rsp);
      `uvm_info(`gfn, $sformatf("Received response: %0s", rsp.convert2string()), UVM_HIGH)
    end : send_req
  endtask

endclass
