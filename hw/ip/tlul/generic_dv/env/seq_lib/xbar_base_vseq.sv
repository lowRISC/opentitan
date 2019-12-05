// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Xbar environment virtual sequence
// ---------------------------------------------
class xbar_base_vseq extends dv_base_vseq #(.CFG_T               (xbar_env_cfg),
                                            .COV_T               (xbar_env_cov),
                                            .VIRTUAL_SEQUENCER_T (xbar_virtual_sequencer));

  // TL host and device sub-sequences
  rand xbar_tl_host_seq  host_seq[];
  rand tl_device_seq     device_seq[];

  uint                   min_req_cnt = 100;
  uint                   max_req_cnt = 200;

  // if seq crosses with the other seq, only need to enable device rsp thread
  bit                    do_device_rsp = 1;

  constraint req_cnt_c {
    foreach (host_seq[i]) {
      host_seq[i].req_cnt inside {[min_req_cnt : max_req_cnt]};
    }
  }

  `uvm_object_utils(xbar_base_vseq)
  `uvm_object_new

  // call seq_init to create and configure host/device seq
  // seq_init needs to be called before randomize as host_seq/device_seq are rand
  function void pre_randomize();
    seq_init();
  endfunction : pre_randomize

  virtual function void seq_init();
    host_seq = new[xbar_hosts.size()];
    device_seq = new[xbar_devices.size()];
    foreach (host_seq[i]) begin
      host_seq[i] = xbar_tl_host_seq::type_id::create(
                    $sformatf("%0s_seq", xbar_hosts[i].host_name));
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
    end
  endfunction : seq_init

  virtual task run_all_device_seq_nonblocking(bit out_of_order_rsp = 1);
    if (do_device_rsp) begin
      foreach (device_seq[i]) begin
        fork
          automatic int device_id = i;
          device_seq[device_id].out_of_order_rsp = out_of_order_rsp;
          device_seq[device_id].start(p_sequencer.device_seqr[device_id]);
        join_none
      end
    end
  endtask

  virtual task run_host_seq(uint host_id);
    host_seq[host_id].valid_host_id_width = cfg.valid_host_id_width;
    host_seq[host_id].start(p_sequencer.host_seqr[host_id]);
    `uvm_info(get_full_name(), $sformatf("%0s finished sending %0d requests",
                               host_seq[host_id].get_full_name(),
                               host_seq[host_id].req_cnt), UVM_LOW)
  endtask

  // run host seq in parallel and use num_enabled_hosts to decide how many hosts to run
  virtual task run_all_host_seq_in_parallel();
    int completed_seq_cnt;
    int host_cnt;
    int host_id_q[$];

    // make host_id_q store all host_id in random order
    foreach (host_seq[i]) host_id_q.push_back(i);
    host_id_q.shuffle();

    foreach (host_id_q[i]) begin
      fork
        automatic int host_id = host_id_q[i];
        begin
          run_host_seq(host_id);
          completed_seq_cnt += 1;
        end
      join_none
      host_cnt++;
      if (host_cnt >= cfg.num_enabled_hosts) break;
    end
    wait(completed_seq_cnt == cfg.num_enabled_hosts);
  endtask

endclass
