// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test creates read buffer eviction by erase operation.
class flash_ctrl_re_evict_vseq extends flash_ctrl_rw_evict_vseq;
  `uvm_object_utils(flash_ctrl_re_evict_vseq)
  `uvm_object_new

  task send_evict(flash_op_t ctrl, int bank);
    erase_flash(ctrl, bank);
  endtask
endclass // flash_ctrl_re_evict_vseq
