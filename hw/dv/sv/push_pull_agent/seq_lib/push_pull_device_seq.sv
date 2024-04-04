// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Response sequence for Push and Pull protocols.
// This sequence will infinitely pol for any DUT requests detected by
// the monitor, and trigger the response driver anytime a request is detected.

class push_pull_device_seq #(parameter int HostDataWidth = 32,
                             parameter int DeviceDataWidth = HostDataWidth)
  extends push_pull_base_seq #(HostDataWidth, DeviceDataWidth);

  `uvm_object_param_utils(push_pull_device_seq#(HostDataWidth, DeviceDataWidth))

  `uvm_object_new

  // Randomizes the device rsp.
  //
  // The randomization works out the same regardless of the agent type.
  virtual function void randomize_item(push_pull_item #(HostDataWidth, DeviceDataWidth) item);
    super.randomize_item(item);
    // If user-provided data is available, use it.
    if (cfg.has_d_user_data()) item.d_data = cfg.get_d_user_data();
  endfunction

  virtual task body();
    if (cfg.agent_type == PushAgent) begin
      push_device_thread();
    end else begin
      pull_device_thread();
    end
  endtask

  // Sends random rsps (assertion of ready) back to host.
  //
  // In Push mode, continuously send an empty but randomized sequence item
  // to the device driver (which just needs to assert ready).
  // If the agent is in bidirectional mode, send the corresponding data.
  // TODO: for bidirectional mode, there may be a need for the returned device data to be
  // constructed based on the received host data. This may need to be made "reactive" as well.
  virtual task push_device_thread();
    forever begin
      wait (!cfg.in_reset);
      `uvm_create(req)
      start_item(req);
      randomize_item(req);
      finish_item(req);
      get_response(rsp);
    end
  endtask

  // Sends random rsps (device data and ack) back to host.
  virtual task pull_device_thread();
    push_pull_item #(HostDataWidth, DeviceDataWidth) req_q[$];
    fork
      forever begin : get_req
        p_sequencer.req_analysis_fifo.get(req);
        req_q.push_back(req);
      end : get_req
      forever begin : send_rsp
        if (cfg.in_reset) begin
          req_q.delete();
          wait (!cfg.in_reset);
        end
        wait (req_q.size());
        rsp = req_q.pop_front();
        start_item(rsp);
        randomize_item(rsp);
        finish_item(rsp);
        get_response(rsp);
      end : send_rsp
    join
  endtask

endclass
