// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Write random size of fraction the page.
// fraction size : [1:16] buswords (4byte).
// Start address is 4byte aligned.
class flash_ctrl_write_rnd_wd_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_write_rnd_wd_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t ctrl;
    int num, bank;
    int mywd;

    // Don't select a partition defined as read-only
    cfg.seq_cfg.avoid_ro_partitions = 1'b1;

    num = 1;
    flash_program_data_c.constraint_mode(0);
    repeat(100) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rand_op)
      ctrl = rand_op;
      bank = rand_op.addr[OTFBankId];
      mywd = fractions;
      prog_flash(ctrl, bank, num, mywd);
    end
  endtask
endclass // flash_ctrl_write_rnd_wd_vseq
