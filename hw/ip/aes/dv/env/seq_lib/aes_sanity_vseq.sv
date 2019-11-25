// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
  class aes_sanity_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_sanity_vseq)

  `uvm_object_new

  task body();

    `uvm_info(`gfn, $sformatf("STARTING AES SEQUENCE"), UVM_LOW);

    `DV_CHECK_RANDOMIZE_WITH_FATAL(aes_item, key_size == 3'b001;)
    set_mode(aes_item.mode);
    set_key_len(aes_item.key_size);
    // add key
    write_key(aes_item.key);

    // add data
    add_data(aes_item.data_in_queue);

    // get cypher
    read_data(aes_item.data_out_queue);

  endtask : body

endclass : aes_sanity_vseq
