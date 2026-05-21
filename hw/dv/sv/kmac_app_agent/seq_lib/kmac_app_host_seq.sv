// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_host_seq extends dv_base_seq #(.REQ         (kmac_app_req_item),
                                              .CFG_T       (kmac_app_agent_cfg),
                                              .SEQUENCER_T (kmac_app_host_sequencer));

  `uvm_object_utils(kmac_app_host_seq)

  // Default to send one data byte, can be overridden at a higher layer.
  // Must be set before this sequence is started.
  //
  // This also implicitly controls when the `last` signal is asserted.
  int unsigned msg_size_bytes = 1;

  extern function new(string name="");
  extern virtual task body();
endclass

function kmac_app_host_seq::new(string name="");
  super.new(name);
endfunction

task kmac_app_host_seq::body();
  int unsigned max_bytes_per_word = MsgWidth / 8;

  while (msg_size_bytes > 0) begin
    int unsigned num_bytes = ((msg_size_bytes >= max_bytes_per_word) ?
                              max_bytes_per_word :
                              msg_size_bytes);

    req = kmac_app_req_item::type_id::create("req");

    start_item(req);

    if (cfg.inject_zero_in_host_strb) begin
      // Drive partial data by setting num_bytes < max_bytes_per_word even when this isn't the last
      // item.
      num_bytes = $urandom_range(1, num_bytes);
    end

    if (!req.randomize() with {
          m_num_bytes == local::num_bytes;
          m_last      == (m_num_bytes == local::msg_size_bytes);
          cfg.req_delay_min <= m_delay; m_delay <= cfg.req_delay_max;
        }) begin
      `uvm_fatal(get_full_name(), "Failed to randomise request.")
    end

    finish_item(req);
    msg_size_bytes -= num_bytes;
  end
endtask
