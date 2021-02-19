// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_host_seq extends keymgr_kmac_base_seq;
  `uvm_object_utils(keymgr_kmac_host_seq)

  `uvm_object_new

  // Default to send one data byte, can be overridden at a higher layer.
  // Must be set before this sequence is started.
  //
  // This also implicitly controls when the `last` signal is asserted.
  int unsigned msg_size_bytes = 1;

  virtual task body();

    `uvm_info(`gfn, $sformatf("msg_size_bytes: %0d", msg_size_bytes), UVM_HIGH)

    cfg.m_data_push_agent_cfg.zero_delays = cfg.zero_delays;
    cfg.m_data_push_agent_cfg.host_delay_min = 1;
    cfg.m_data_push_agent_cfg.host_delay_max = 100;

    req = keymgr_kmac_item::type_id::create("req");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req, byte_data_q.size() == msg_size_bytes;)
    `uvm_info(`gfn, $sformatf("Randomized req: %0s", req.sprint()), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("byte_data_q: %0p", req.byte_data_q), UVM_HIGH)

    while (msg_size_bytes > 0) begin

      bit [KmacDataIfWidth-1:0] req_data = '0;
      bit [KmacDataIfWidth/8-1:0] req_strb = '0;
      bit req_last = 0;

      // create push_pull_host_seq
      push_pull_host_seq#(`CONNECT_DATA_WIDTH) host_seq;
      `uvm_create_on(host_seq, p_sequencer.m_push_pull_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(host_seq)

      // Assemble the message chunk and strb
      for (int i = 0; i < KmacDataIfWidth / 8; i ++) begin
        if (msg_size_bytes == 0) break;

        req_data[i*8 +: 8] = 8'(req.byte_data_q.pop_front());

        req_strb[i] = 1'b1;

        msg_size_bytes -= 1;
      end


      // Set the last bit
      req_last = (msg_size_bytes == 0);

      cfg.m_data_push_agent_cfg.add_h_user_data({req_data, req_strb, req_last});

      `uvm_send(host_seq)

    end
  endtask

endclass
