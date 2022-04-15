// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Enable OpGenHwOut to test sideload key to a selected interface
class keymgr_sideload_one_intf_vseq extends keymgr_sideload_vseq;
  `uvm_object_utils(keymgr_sideload_one_intf_vseq)
  `uvm_object_new

  keymgr_pkg::keymgr_key_dest_e sideload_dest = keymgr_pkg::None;
  // also test HW sideload
  constraint gen_operation_c {
    gen_operation == keymgr_pkg::OpGenHwOut;
  }

  constraint key_dest_c {
    key_dest == sideload_dest;
  }

  constraint do_clear_sideload_c {
   do_clear_sideload == 1;
  }

  function void pre_randomize();
    `DV_GET_ENUM_PLUSARG(keymgr_pkg::keymgr_key_dest_e, sideload_dest, sideload_dest, 1)
    super.pre_randomize();
  endfunction
endclass : keymgr_sideload_one_intf_vseq
