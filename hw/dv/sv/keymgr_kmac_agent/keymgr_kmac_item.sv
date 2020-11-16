// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_item extends uvm_sequence_item;

  // random variables
  rand byte               byte_data_q[$];
  rand bit [KeyWidth-1:0] rsp_digest_share0;
  rand bit [KeyWidth-1:0] rsp_digest_share1;
  rand bit                rsp_error;

  rand int unsigned       rsp_delay;

  constraint rsp_error_c {
    soft rsp_error == 0;
  }

  `uvm_object_utils_begin(keymgr_kmac_item)
    `uvm_field_queue_int(byte_data_q, UVM_DEFAULT)
    `uvm_field_int(rsp_digest_share0, UVM_DEFAULT)
    `uvm_field_int(rsp_digest_share1, UVM_DEFAULT)
    `uvm_field_int(rsp_error,         UVM_DEFAULT)
    `uvm_field_int(rsp_delay,         UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
