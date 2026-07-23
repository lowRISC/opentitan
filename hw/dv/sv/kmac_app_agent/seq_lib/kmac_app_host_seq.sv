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

  // Configure whether this sequence is being run on a masked interface. If this is false, all
  // items are constrained to have m_data_s1 == '0. If this is true, items before the last cannot
  // have m_num_bytes < MsgWidth/8.
  bit          m_using_masked_interface = 1'b1;

  // If true, the last bytes in the sequence will be in an item with m_last == 0, which will be
  // followed by one last item with m_num_bytes == 0 and m_last == 1.
  rand bit     m_use_explicit_empty_message;

  extern function new(string name="");
  extern virtual task body();
endclass

function kmac_app_host_seq::new(string name="");
  super.new(name);
endfunction

task kmac_app_host_seq::body();
  int unsigned max_bytes_per_word = MsgWidth / 8;
  int unsigned bytes_remaining = msg_size_bytes;

  forever begin
    int unsigned num_bytes = ((bytes_remaining >= max_bytes_per_word) ?
                              max_bytes_per_word :
                              bytes_remaining);

    req = kmac_app_req_item::type_id::create("req");

    start_item(req);

    // If not using masking, we can drive partial data even when this isn't the last item.
    if (cfg.inject_zero_in_host_strb && !m_using_masked_interface) begin
      num_bytes = $urandom_range(0, num_bytes);
    end

    if (!req.randomize() with {
          // The second share should be zero unless masking is in use
          !local::m_using_masked_interface -> ~|m_data_s1;

          m_num_bytes == local::num_bytes;

          // Set the m_last flag on the last item that will be sent. If m_use_explicit_empty_message
          // is true, this is an extra empty item that is generated after the last one with some
          // data.
          m_last      == ((local::num_bytes == local::bytes_remaining) &&
                          ((local::num_bytes == 0) || !local::m_use_explicit_empty_message));

          cfg.req_delay_min <= m_delay; m_delay <= cfg.req_delay_max;
        }) begin
      `uvm_fatal(get_full_name(), "Failed to randomise request.")
    end

    finish_item(req);
    bytes_remaining -= num_bytes;

    // If req.m_last was true then we just sent the last item and should stop.
    if (req.m_last) break;
  end
endtask
