// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Request sequence for Push and Pull protocols.
//
// Similiar push_pull_host_seq, this sequence will send an unlimited number of requests to
// the DUT. It is the responsibility of the parent sequence to halt this sequence by setting
// the stop field.
//

class push_pull_indefinite_host_seq #(parameter int HostDataWidth = 32,
                                      parameter int DeviceDataWidth = HostDataWidth)
  extends push_pull_base_seq #(HostDataWidth, DeviceDataWidth);

  `uvm_object_param_utils(push_pull_indefinite_host_seq#(HostDataWidth, DeviceDataWidth))

  `uvm_object_new

  bit do_stop;

  virtual task body();
    while (!do_stop) begin : send_req
      `uvm_create(req)
      start_item(req);
      randomize_item(req);
      finish_item(req);
      get_response(rsp);
    end : send_req
  endtask

  virtual task stop();
    do_stop = 1;
  endtask

  virtual task pre_start();
    super.pre_start();
    do_stop = 0;
  endtask
endclass
