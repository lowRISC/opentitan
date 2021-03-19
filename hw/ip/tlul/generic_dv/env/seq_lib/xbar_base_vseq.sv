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
  rand bit               en_req_abort;
  rand bit               en_rsp_abort;

  uint                   min_req_cnt = 100;
  uint                   max_req_cnt = 200;

  // if seq crosses with the other seq, only need to enable device rsp thread
  bit                    do_device_rsp = 1;

  constraint req_cnt_c {
    foreach (host_seq[i]) {
      host_seq[i].req_cnt inside {[min_req_cnt : max_req_cnt]};
    }
  }

  constraint en_req_abort_c {
    en_req_abort dist {
      1 :/ 25,
      0 :/ 75
    };
  }

  constraint en_rsp_abort_c {
    en_rsp_abort dist {
      1 :/ 25,
      0 :/ 75
    };
  }
  `uvm_object_utils(xbar_base_vseq)
  `uvm_object_new

  // create and configure host/device seq before randomize as host_seq/device_seq are rand
  function void pre_randomize();
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
      device_seq[i] = tl_device_seq#()::type_id::create(
                      $sformatf("%0s_seq", xbar_devices[i].device_name));
      device_seq[i].d_error_pct = $urandom_range(0, 70);
    end
  endfunction : pre_randomize

  function void post_randomize();
    foreach (host_seq[i]) begin
      if (en_req_abort) host_seq[i].req_abort_pct = $urandom_range(0, 100);
    end
    foreach (device_seq[i]) begin
      if (en_rsp_abort) device_seq[i].rsp_abort_pct = $urandom_range(0, 100);
    end
  endfunction : post_randomize

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
