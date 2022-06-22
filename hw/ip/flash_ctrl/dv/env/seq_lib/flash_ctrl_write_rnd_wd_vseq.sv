// Copyright lowRISC contributors.
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
    int mywd = 1;

    flash_ctrl_default_region_cfg(,,,MuBi4True,MuBi4True);

    ctrl.partition  = FlashPartData;
    ctrl.otf_addr = is_addr_odd * 4;
    bank = $urandom_range(0,1);
    num = 1;
    repeat(100) begin
      mywd = fractions;
      prog_flash(ctrl, bank, num, mywd);
    end
  endtask
endclass // flash_ctrl_write_rnd_wd_vseq
