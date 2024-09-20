// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send write only traffic
class flash_ctrl_wo_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_wo_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t ctrl;
    int num, bank;

    // Don't select a partition defined as read-only
    cfg.seq_cfg.avoid_ro_partitions = 1'b1;

    flash_program_data_c.constraint_mode(0);

    repeat(100) begin
      if (cfg.stop_transaction_generators()) break;
      `DV_CHECK(try_create_prog_op(ctrl, bank, num), "Could not create a prog flash op")
      prog_flash(ctrl, bank, num);
    end
  endtask
endclass : flash_ctrl_wo_vseq
