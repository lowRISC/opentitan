// Copyright lowRISC contributors (OpenTitan project).
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
  extends push_pull_host_seq #(HostDataWidth, DeviceDataWidth);

  `uvm_object_param_utils(push_pull_indefinite_host_seq#(HostDataWidth, DeviceDataWidth))

  `uvm_object_new

  int items_processed;

  typedef enum int {
    Continue = 0,
    Stop     = 1,
    HardStop = 2
  } stop_status_e;

  stop_status_e stop_status;

  task wait_for_items_processed(int n);
    wait(items_processed >= n);
  endtask

  virtual task body();
    items_processed = 0;
    fork : isolation_fork
      begin
        fork
          begin
            wait(stop_status == HardStop);
            `uvm_info(`gfn, "Rec'd stop message", UVM_FULL)
          end
          while (stop_status == Continue) begin : send_req
            `uvm_create(req)
            start_item(req);
            randomize_item(req);
            finish_item(req);
            get_response(rsp);
            items_processed++;
          end : send_req
        join_any;
        disable fork;
      end
    join : isolation_fork
    `uvm_info(`gfn, "STOPPED", UVM_FULL)
  endtask

  virtual task stop(bit hard = 1);
    stop_status = hard ? HardStop : Stop;
  endtask

  virtual task pre_start();
    super.pre_start();
    stop_status = Continue;
  endtask
endclass
