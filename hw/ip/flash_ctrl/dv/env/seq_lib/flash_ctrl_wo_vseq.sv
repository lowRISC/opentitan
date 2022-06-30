// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send write only traffic
class flash_ctrl_wo_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_wo_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t ctrl;
    int num, bank;
    ctrl.partition  = FlashPartData;

//    repeat(100) begin
      num = 1;//$urandom_range(1, 32);
      bank = 0;//$urandom_range(0, 1);
//      prog_flash(swcmd, bank, num, 2);
    ctrl.otf_addr = 4;
      prog_flash(ctrl, bank, num, 2);
//    end
  endtask
endclass // flash_ctrl_wo_vseq
