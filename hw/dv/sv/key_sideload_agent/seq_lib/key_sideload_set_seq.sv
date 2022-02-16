// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class key_sideload_set_seq #(
    parameter type KEY_T = keymgr_pkg::hw_key_req_t
) extends key_sideload_base_seq #(KEY_T);

  `uvm_object_utils(key_sideload_set_seq#(KEY_T))

  `uvm_object_new
  rand KEY_T sideload_key;

  virtual task body();
    key_sideload_item#(KEY_T) item;
    item = key_sideload_item#(KEY_T)::type_id::create("item");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(item,
                                   item.valid == sideload_key.valid;
                                   item.key0 == sideload_key.key[0];
                                   item.key1 == sideload_key.key[1];)
    start_item(item);
    finish_item(item);
    get_response(item);
  endtask

endclass
