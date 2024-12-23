// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic smoke test vseq
class flash_ctrl_smoke_vseq extends flash_ctrl_rand_ops_base_vseq;
  `uvm_object_utils(flash_ctrl_smoke_vseq)

  `uvm_object_new

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();
    // Do fewer reruns for the smoke test.
    cfg.seq_cfg.max_num_trans = 2;

    // Do fewer flash ops in each rerun for the smoke test.
    cfg.seq_cfg.max_flash_ops_per_cfg = 4;

    // Do no more than 128 words per op.
    cfg.seq_cfg.op_max_words = 128;

    // Don't enable any memory protection.
    cfg.seq_cfg.num_en_mp_regions = 0;

    cfg.seq_cfg.set_partition_pc(.sel_data_part_pc(100),
                                 .sel_info_part_pc(0),
                                 .sel_info1_part_pc(0),
                                 .sel_info2_part_pc(0));

    // Don't enable access to any of information partitions.
    foreach (cfg.seq_cfg.mp_info_page_en_pc[i, j]) begin
      cfg.seq_cfg.mp_info_page_en_pc[i][j] = 0;
    end

    // Enable default region read/program and erasability.
    cfg.seq_cfg.default_region_read_en_pc = 100;
    cfg.seq_cfg.default_region_program_en_pc = 100;
    cfg.seq_cfg.default_region_erase_en_pc = 100;

    // Allow banks to be erased.
    cfg.seq_cfg.bank_erase_en_pc = 100;

    cfg.seq_cfg.poll_fifo_status_pc = 0;
  endfunction

endclass : flash_ctrl_smoke_vseq
