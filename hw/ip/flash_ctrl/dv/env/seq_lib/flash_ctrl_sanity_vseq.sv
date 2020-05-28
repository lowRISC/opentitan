// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class flash_ctrl_sanity_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_sanity_vseq)

  `uvm_object_new

  task body();
    `uvm_error(`gfn, "FIXME")
  endtask : body

endclass : flash_ctrl_sanity_vseq
