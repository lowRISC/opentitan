// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_keymgr_sideload_kmac_vseq extends chip_sw_keymgr_key_derivation_vseq;
  `uvm_object_utils(chip_sw_keymgr_sideload_kmac_vseq)

  `uvm_object_new

  virtual task check_op_in_owner_int_state(bit [keymgr_pkg::KeyWidth-1:0] unmasked_key);
    check_kmac_sideload(unmasked_key);
    // TODO, check the result of the kmac operation with the sideload key
  endtask
endclass : chip_sw_keymgr_sideload_kmac_vseq
