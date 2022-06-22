// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send write only traffic
// Starting from 1 busword (4byte), increases by 1 word each round
// To avoid program window violation, word size modular by 16.
class flash_ctrl_write_word_sweep_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_write_word_sweep_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t ctrl;
    int num, bank;
     int mywd = 1;

    ctrl.partition  = FlashPartData;
    bank = $urandom_range(0,1);
    num = 2;
    ctrl.otf_addr = 4;
    mywd = 2;
//    repeat(3) begin
      prog_flash(ctrl, bank, num, mywd);
//      mywd = (mywd % 16) + 1;
//    end
  endtask
endclass // flash_ctrl_wo_vseq
