// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class aes_sanity_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_sanity_vseq)

  `uvm_object_new

  task body();

    `uvm_info(`gfn, $sformatf("STARTING AES SEQUENCE"), UVM_LOW);
    `DV_CHECK_RANDOMIZE_FATAL(this)
    `uvm_info(`gfn, $sformatf("running aes sanity sequence"), UVM_LOW);

  endtask : body

endclass : aes_sanity_vseq


