// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Read random size of fraction the page.
// fraction size : [1:16] buswords (4byte).
// Start address is 4byte aligned.
class flash_ctrl_read_rnd_wd_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_read_rnd_wd_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t ctrl;
    int num, bank;
    int mywd;

    num = 1;
    flash_program_data_c.constraint_mode(0);
    repeat(100) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rand_op)
      ctrl = rand_op;
      bank = rand_op.addr[OTFBankId];
      mywd = fractions;
      read_flash(ctrl, bank, num, mywd);
    end
  endtask
endclass // flash_ctrl_read_rnd_wd_vseq
