// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Starting from 2 busword (4byte), increases by 2 words each round
// To avoid program window violation, word size never exceeeds 16.
class flash_ctrl_write_word_sweep_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_write_word_sweep_vseq)
  `uvm_object_new

  constraint ctrl_num_c {ctrl_num == 1;}
  constraint fractions_c {fractions == 2;}
  virtual task body();
    flash_op_t ctrl;
    int num, bank;
    int mywd;

    // Don't select a partition defined as read-only
    cfg.seq_cfg.avoid_ro_partitions = 1'b1;
    `DV_CHECK(try_create_prog_op(ctrl, bank, num), "Could not create a prog flash op")
    mywd = fractions;
    `DV_CHECK_EQ(mywd, 2)
    repeat(10) begin
      prog_flash(ctrl, bank, num, mywd);
      mywd = (mywd % 16) + 2;
    end
  endtask
endclass : flash_ctrl_write_word_sweep_vseq
