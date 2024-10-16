// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send write only traffic
class flash_ctrl_intr_wr_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_intr_wr_vseq)
  `uvm_object_new

  constraint ctrl_data_num_c {ctrl_data_num inside {[1 : 32]};}

  task pre_start();
    cfg.intr_mode = 1;
    super.pre_start();
  endtask

  virtual task body();
    flash_op_t ctrl;
    int num, bank;

    // Don't select a partition defined as read-only
    cfg.seq_cfg.avoid_ro_partitions = 1'b1;
    flash_program_data_c.constraint_mode(0);
    repeat(100) begin
      `DV_CHECK(try_create_prog_op(ctrl, bank, num), "Could not create a prog flash op")
      prog_flash(ctrl, bank, num, fractions);
    end
  endtask
endclass : flash_ctrl_intr_wr_vseq
