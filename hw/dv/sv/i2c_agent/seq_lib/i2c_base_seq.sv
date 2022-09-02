// Copyright lowRISC contributors.
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
  i2c_item req_q[$];

  // data to be sent to target dut
  bit [7:0] data_q[$];
  // constrain size of data sent/received
  constraint data_q_size_c {
    data_q.size() inside {[cfg.i2c_host_min_data_rw : cfg.i2c_host_max_data_rw]};
  }

  virtual task body();
    if (cfg.if_mode == Device) begin
      // get seq for agent running in Device mode
      fork
        forever begin
          i2c_item req;
          p_sequencer.req_analysis_fifo.get(req);
          req_q.push_back(req);
        end
        forever begin
          i2c_item rsp;
          wait(req_q.size > 0);
          rsp = req_q.pop_front();
          start_item(rsp);
          finish_item(rsp);
        end
      join
    end else begin
      // get seq for agent running in Host mode
      req = i2c_item::type_id::create("req");
      start_item(req);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
                                     data_q.size() == local::data_q.size();
                                     foreach (data_q[i]) {
                                       data_q[i] == local::data_q[i];
                                     })
      finish_item(req);
      get_response(rsp);
    end
  endtask : body

endclass : i2c_base_seq
