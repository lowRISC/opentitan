// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Read fraction of the page.
// fraction size starts from 1 word (4byte) and increased by 1 word in each round.
class flash_ctrl_read_word_sweep_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_read_word_sweep_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t ctrl, host;
    int num, bank;
    int mywd;

    ctrl = rand_op;
    bank = rand_op.addr[OTFBankId];
    num = 1;
    mywd = 1;
    repeat(20) begin
      read_flash(ctrl, bank, num, mywd);
      mywd = (mywd % 16) + 1;
    end
  endtask

endclass // flash_ctrl_read_word_sweep_vseq
