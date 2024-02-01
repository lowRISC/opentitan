// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_base_seq extends dv_base_seq #(
    .REQ         (i2c_item),
    .CFG_T       (i2c_agent_cfg),
    .SEQUENCER_T (i2c_sequencer)
  );
  `uvm_object_utils(i2c_base_seq)
  `uvm_object_new

  // queue monitor requests which ask the re-active driver to response host dut
  REQ req_q[$];

  // data to be sent to target dut
  bit [7:0] data_q[$];

  // Stops running this sequence
  protected bit stop;
  // constrain size of data sent/received
  constraint data_q_size_c {
    data_q.size() inside {[cfg.i2c_host_min_data_rw : cfg.i2c_host_max_data_rw]};
  }

  virtual task body();
    if (cfg.if_mode == Device) begin
      send_device_mode_txn();
    end else begin
      send_host_mode_txn();
    end
  endtask : body

  virtual task send_device_mode_txn();
    // get seq for agent running in Device mode
    bit [7:0] rdata;
    forever begin
      p_sequencer.req_analysis_fifo.get(req);
      // if it's a read type response, randomize the return data
      if (req.drv_type == RdData) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(rdata)
        req.rdata = rdata;
      end
      start_item(req);
      finish_item(req);
    end
  endtask

  virtual task send_host_mode_txn();
    // get seq for agent running in Host mode
    req = REQ::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
                                   data_q.size() == local::data_q.size();
                                   foreach (data_q[i]) {
                                     data_q[i] == local::data_q[i];
                                   })
    finish_item(req);
    get_response(rsp);
  endtask

  virtual task seq_stop();
    stop = 1'b1;
    wait_for_sequence_state(UVM_FINISHED);
  endtask : seq_stop

endclass : i2c_base_seq
