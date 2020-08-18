// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Response sequence for Push and Pull protocols.
// This sequence will infinitely pol for any DUT requests detected by
// the monitor, and trigger the response driver anytime a request is detected.

class push_pull_device_seq #(parameter int DataWidth = 32) extends push_pull_base_seq #(DataWidth);

  `uvm_object_param_utils(push_pull_device_seq#(DataWidth))

  `uvm_object_new

  mailbox #(push_pull_item#(DataWidth)) req_mailbox;

  virtual task body();
    req_mailbox = new();

    if (cfg.agent_type == PushAgent) begin
      // In Push mode, continuously send an empty but randomized sequence item
      // to the device driver (which just needs to assert ready).
      forever begin
        req = push_pull_item#(DataWidth)::type_id::create("req");
        start_item(req);
        `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
          if (cfg.zero_delays) {
            device_delay == 0;
          } else {
            device_delay inside {[cfg.device_delay_min : cfg.device_delay_max]};
          }
        )
        finish_item(req);
        get_response(rsp);
        `uvm_info(`gfn, $sformatf("Received response: %0s", rsp.convert2string()), UVM_HIGH)
      end
    end else begin
      fork
        forever begin : collect_req
          // We indefinitely poll for any traffic sent from the monitor and store it to a mailbox.
          p_sequencer.req_fifo.get(req);
          req_mailbox.put(req);
        end : collect_req
        forever begin : send_req
          // Collect transactions stored in the mailbox and send them to the driver.
          req_mailbox.get(rsp);
          start_item(rsp);
          `DV_CHECK_RANDOMIZE_WITH_FATAL(rsp,
            if (cfg.zero_delays) {
              device_delay == 0;
            } else {
              device_delay inside {[cfg.device_delay_min : cfg.device_delay_max]};
            }
          )
          finish_item(rsp);
          get_response(rsp);
          `uvm_info(`gfn, $sformatf("Received response: %0s", rsp.convert2string()), UVM_HIGH)
        end : send_req
      join
    end
  endtask

endclass
