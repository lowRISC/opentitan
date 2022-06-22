// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_rw_vseq extends flash_ctrl_otf_vseq;
  `uvm_object_utils(flash_ctrl_rw_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t swcmd;
    int num, bank;
    swcmd.partition  = FlashPartData;

    repeat(500) begin
      num = $urandom_range(1, 32);
      bank = $urandom_range(0, 1);
      randcase
        1:prog_flash(swcmd, bank, num);
        1:read_flash(swcmd, bank, num);
      endcase
    end
  endtask
endclass // flash_ctrl_rw_vseq
