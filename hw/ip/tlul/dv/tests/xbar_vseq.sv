// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Xbar environment virtual sequence
// ---------------------------------------------
class xbar_vseq extends uvm_sequence;

  // TL host and device sub-sequences
  rand xbar_tl_host_seq  host_seq[];
  rand tl_device_seq     device_seq[];

  // Runtime options
  int unsigned           min_req_cnt = 100;
  int unsigned           max_req_cnt = 200;
  int unsigned           min_req_delay = 0;
  int unsigned           max_req_delay = 20;
  int unsigned           min_rsp_delay = 0;
  int unsigned           max_rsp_delay = 20;

  constraint req_cnt_c {
    foreach (host_seq[i]) {
      host_seq[i].req_cnt inside {[min_req_cnt : max_req_cnt]};
    }
  }

  `uvm_object_utils(xbar_vseq)
  `uvm_declare_p_sequencer(xbar_vseqr)

  function new (string name = "");
    super.new(name);
    void'($value$plusargs("min_req_cnt=%d",   min_req_cnt));
    void'($value$plusargs("max_req_cnt=%d",   max_req_cnt));
    void'($value$plusargs("min_req_delay=%d", min_req_delay));
    void'($value$plusargs("max_req_delay=%d", max_req_delay));
    void'($value$plusargs("min_rsp_delay=%d", min_rsp_delay));
    void'($value$plusargs("max_rsp_delay=%d", max_rsp_delay));
    host_seq = new[xbar_hosts.size()];
    device_seq = new[xbar_devices.size()];
    foreach (host_seq[i]) begin
      host_seq[i] = xbar_tl_host_seq::type_id::create(
                    $sformatf("%0s_seq", xbar_hosts[i].host_name));
      host_seq[i].min_req_delay = min_req_delay;
      host_seq[i].max_req_delay = max_req_delay;
      // Default only send request to valid devices that is accessible by the host
      foreach (xbar_devices[j]) begin
        if (is_valid_path(xbar_hosts[i].host_name, xbar_devices[j].device_name)) begin
          `uvm_info(get_full_name, $sformatf("Add device %0s to seq %0s",
                    xbar_devices[i].device_name, host_seq[i].get_name()), UVM_HIGH)
          host_seq[i].valid_device_id.push_back(j);
        end
      end
    end
    foreach (device_seq[i]) begin
      device_seq[i] = tl_device_seq::type_id::create(
                      $sformatf("%0s_seq", xbar_devices[i].device_name));
      device_seq[i].min_rsp_delay = min_rsp_delay;
      device_seq[i].max_rsp_delay = max_rsp_delay;
    end
  endfunction : new

  virtual task body();
    int completed_seq;
    foreach (device_seq[i]) begin
      fork
        automatic int device_id = i;
        device_seq[device_id].start(p_sequencer.device_seqr[device_id]);
      join_none
    end
    foreach (host_seq[i]) begin
      fork
        automatic int host_id = i;
        begin
          host_seq[host_id].start(p_sequencer.host_seqr[host_id]);
          `uvm_info(get_full_name(), $sformatf("%0s finished sending %0d requests",
                                     host_seq[host_id].get_full_name(),
                                     host_seq[host_id].req_cnt), UVM_LOW)
          completed_seq += 1;
        end
      join_none
    end
    wait (completed_seq == host_seq.size());
  endtask

endclass
