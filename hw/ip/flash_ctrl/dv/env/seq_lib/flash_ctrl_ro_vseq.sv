// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send read only traffic
// No protection is applied.
// TB memory model is disabled.
class flash_ctrl_ro_vseq extends flash_ctrl_otf_vseq;
  `uvm_object_utils(flash_ctrl_ro_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t swcmd;
    int num, bank;
    swcmd.partition  = FlashPartData;

    repeat(100) begin
      num = $urandom_range(1, 32);
       bank = $urandom_range(0, 2);

      read_flash(swcmd, 0, num);
    end
  endtask

endclass // flash_ctrl_ro_vseq
