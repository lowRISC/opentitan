// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_item extends uvm_sequence_item;

  // random variables

  // request data/mask
  //
  // also used by the monitor to assemble the full request message
  rand byte byte_data_q[$];

  // response digest/error
  rand bit [kmac_pkg::AppDigestW-1:0] rsp_digest_share0;
  rand bit [kmac_pkg::AppDigestW-1:0] rsp_digest_share1;
  rand bit                            rsp_error;

  rand int unsigned       rsp_delay;

  `uvm_object_utils_begin(kmac_app_item)
    `uvm_field_queue_int(byte_data_q, UVM_DEFAULT)
    `uvm_field_int(rsp_digest_share0, UVM_DEFAULT)
    `uvm_field_int(rsp_digest_share1, UVM_DEFAULT)
    `uvm_field_int(rsp_error,         UVM_DEFAULT)
    `uvm_field_int(rsp_delay,         UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function bit get_is_kmac_rsp_data_invalid();
    return is_constant_share(rsp_digest_share0) || is_constant_share(rsp_digest_share1);
  endfunction

  static function bit is_constant_share(bit [kmac_pkg::AppDigestW-1:0] share);
    return share inside {'0, '1};
  endfunction

endclass
