// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_item extends uvm_sequence_item;

  // below 3 cases will trigger KMAC invalid output error
  `define CALC_KMAC_DATA_INVALID \
      (rsp_digest_share0 inside {0, '1} || rsp_digest_share1 inside {0, '1})

  // random variables

  // request data/mask
  //
  // also used by the monitor to assemble the full request message
  rand byte byte_data_q[$];

  // response digest/error
  rand bit [KeyWidth-1:0] rsp_digest_share0;
  rand bit [KeyWidth-1:0] rsp_digest_share1;
  rand bit                rsp_error;

  rand bit                is_kmac_rsp_err;
  rand int unsigned       rsp_delay;

  constraint is_kmac_rsp_err_c {
    (`CALC_KMAC_DATA_INVALID || rsp_error) == is_kmac_rsp_err;
  }

  `uvm_object_utils_begin(keymgr_kmac_item)
    `uvm_field_queue_int(byte_data_q, UVM_DEFAULT)
    `uvm_field_int(rsp_digest_share0, UVM_DEFAULT)
    `uvm_field_int(rsp_digest_share1, UVM_DEFAULT)
    `uvm_field_int(rsp_error,         UVM_DEFAULT)
    `uvm_field_int(is_kmac_rsp_err,   UVM_DEFAULT)
    `uvm_field_int(rsp_delay,         UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function bit get_is_kmac_rsp_data_invalid();
    return `CALC_KMAC_DATA_INVALID;
  endfunction

  `undef CALC_KMAC_DATA_INVALID
endclass
