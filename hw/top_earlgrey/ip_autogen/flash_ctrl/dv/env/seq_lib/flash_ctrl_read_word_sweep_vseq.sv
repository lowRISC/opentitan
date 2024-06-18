// Copyright lowRISC contributors (OpenTitan project).
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

    begin
      flash_op_t prog_op;
      int progwd = 16;
      ctrl_num = 12;
      ctrl_num.rand_mode(0);
      fractions = 16;
      fractions.rand_mode(0);
      `DV_CHECK(try_create_prog_op(ctrl, bank, num), "Could not create a prog flash op")
      prog_op = ctrl;
      print_flash_op(prog_op, UVM_MEDIUM);
      prog_flash(prog_op, bank, num, fractions);
    end
    num = 1;
    mywd = 1;
    repeat(20) begin
      read_flash(ctrl, bank, num, mywd);
      mywd = (mywd % 16) + 1;
    end
  endtask

endclass : flash_ctrl_read_word_sweep_vseq
