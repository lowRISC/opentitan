// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class key_sideload_set_seq #(
    parameter type KEY_T = keymgr_pkg::hw_key_req_t
) extends key_sideload_base_seq #(KEY_T);

  `uvm_object_utils(key_sideload_set_seq#(KEY_T))

  rand KEY_T sideload_key;

  // The (single) item that is created and run
  local key_sideload_item#(KEY_T) m_item;

  // A flag that shows request_stop has run, and no item should be created or run.
  local bit m_stop_requested;

  function new (string name="");
    super.new(name);
  endfunction

  virtual task body();
    m_item = key_sideload_item#(KEY_T)::type_id::create("m_item");
    if (m_stop_requested) return;

    start_item(m_item);

    if (!m_item.randomize() with {
          m_item.valid == sideload_key.valid;
          m_item.key0 == sideload_key.key[0];
          m_item.key1 == sideload_key.key[1];
        }) begin
      `uvm_fatal(get_name(), "Failed to randomize m_item.")
    end

    if (m_stop_requested) begin
      // m_stop_requested must have been set when we were waiting to start the item. Since it has
      // started, we have to call finish (to avoid the sequencer locking up). Since we don't
      // actually want the item to do anything, we just call request_stop on it now.
      m_item.request_stop();
    end

    finish_item(m_item);
    if (m_stop_requested) return;

    get_response(m_item);
  endtask

  // If the sequence is running an item, send a message to the driver running that item to ask that
  // driver to abort the item, which will complete the sequence.
  function void request_stop();
    m_stop_requested = 1;

    if (m_item != null) begin
      m_item.request_stop();
    end
  endfunction

endclass
