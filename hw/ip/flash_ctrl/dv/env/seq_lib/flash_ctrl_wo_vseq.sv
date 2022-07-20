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
    flash_ctrl_default_region_cfg();//,,,MuBi4True,MuBi4True);

    ctrl.partition  = FlashPartData;
//    repeat(100) begin
//      num = $urandom_range(1, 32);
//      bank = $urandom_range(0, 1);
//      prog_flash(ctrl, bank, num);
//    end
    repeat(2) prog_flash(ctrl, 0, 1, 1);

    ctrl.otf_addr = 0;
    read_flash(ctrl, 0, 1, 2);
  endtask
endclass // flash_ctrl_wo_vseq
