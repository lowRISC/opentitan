// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class key_sideload_set_seq extends key_sideload_base_seq;
  `uvm_object_utils(key_sideload_set_seq)

  `uvm_object_new
  rand keymgr_pkg::hw_key_req_t sideload_key;

  virtual task body();
    key_sideload_item item;
    item = key_sideload_item::type_id::create("item");
    start_item(item);
    item.valid = sideload_key.valid;
    item.key0  = sideload_key.key[0];
    item.key1  = sideload_key.key[1];
    finish_item(item);
    get_response(item);
  endtask

endclass
