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

    flash_program_data_c.constraint_mode(0);

    repeat(100) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rand_op)
      ctrl = rand_op;
      if (ctrl.partition == FlashPartData) begin
        num = $urandom_range(1, 32);
      end else begin
        num = $urandom_range(1, InfoTypeSize[rand_op.partition >> 1]);
      end
      bank = rand_op.addr[OTFBankId];
      prog_flash(ctrl, bank, num);
    end
  endtask
endclass // flash_ctrl_wo_vseq
