// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_keymgr_sideload_kmac_vseq extends chip_sw_keymgr_key_derivation_vseq;
  `uvm_object_utils(chip_sw_keymgr_sideload_kmac_vseq)

  `uvm_object_new

  // The following varibles match their SW side equivalents
  localparam int MessageBytes = 4;
  localparam bit [7:0] MsgArr[MessageBytes] = {8'h00, 8'h01, 8'h02, 8'h03};
  localparam string CustomStr = "";
  localparam int DigestBytes = 32;
  localparam int KeyBytes = keymgr_pkg::KeyWidth / 8;

  virtual task check_op_in_owner_int_state(bit [keymgr_pkg::KeyWidth-1:0] unmasked_key);
    bit [keymgr_pkg::KeyWidth-1:0] sideload_kmac_key;
    bit [7:0] sideload_key_arr[KeyBytes];
    bit [7:0] digest_arr[DigestBytes];

    check_kmac_sideload(unmasked_key, sideload_kmac_key);

    {<< byte {sideload_key_arr}} = sideload_kmac_key;

    c_dpi_kmac128(MsgArr, MessageBytes,
                  sideload_key_arr, KeyBytes,
                  CustomStr,
                  DigestBytes, digest_arr);

    sw_symbol_backdoor_overwrite("sideload_digest_result", digest_arr);
  endtask

endclass : chip_sw_keymgr_sideload_kmac_vseq
