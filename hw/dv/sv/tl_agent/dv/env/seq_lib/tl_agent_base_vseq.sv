// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// tl_agent environment virtual sequence
// ---------------------------------------------
class tl_agent_base_vseq extends dv_base_vseq #(.CFG_T               (tl_agent_env_cfg),
                                                .COV_T               (tl_agent_env_cov),
                                                .VIRTUAL_SEQUENCER_T (tl_agent_virtual_sequencer));
  uint min_req_cnt = 100;
  uint max_req_cnt = 200;

  rand bit out_of_order_rsp = 1;

  `uvm_object_utils(tl_agent_base_vseq)
  `uvm_object_new

  virtual task run_device_seq_nonblocking();
    fork begin
      tl_device_seq device_seq;
      device_seq = tl_device_seq::type_id::create("device_seq");
      `DV_CHECK_RANDOMIZE_FATAL(device_seq)
      device_seq.out_of_order_rsp = out_of_order_rsp;
      device_seq.start(p_sequencer.device_seqr);
    end join_none
  endtask

  virtual task run_host_seq();
    tl_host_seq host_seq;
    host_seq = tl_host_seq::type_id::create("host_seq");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(host_seq,
                                   req_cnt inside {[min_req_cnt : max_req_cnt]};)
    host_seq.start(p_sequencer.host_seqr);
    `uvm_info(`gfn, $sformatf("host_seq finished sending %0d requests", host_seq.req_cnt), UVM_LOW)
  endtask

  virtual task body();
    run_device_seq_nonblocking();
    repeat (num_trans) run_host_seq();
  endtask

endclass
