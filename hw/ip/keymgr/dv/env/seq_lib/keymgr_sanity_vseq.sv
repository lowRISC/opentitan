// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class keymgr_sanity_vseq extends keymgr_base_vseq;
  `uvm_object_utils(keymgr_sanity_vseq)

  `uvm_object_new


  task body();
    `uvm_info(`gfn, "Key manager sanity check", UVM_LOW)
    // to creator root
    keymgr_advance();
    keymgr_generate(1);
    keymgr_rd_clr();

    keymgr_advance();
    keymgr_generate(1);
    keymgr_rd_clr();

    keymgr_advance();
    keymgr_advance();
    keymgr_advance();
  endtask : body

endclass : keymgr_sanity_vseq
