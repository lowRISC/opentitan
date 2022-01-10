// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class rom_ctrl_smoke_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_smoke_vseq)

  `uvm_object_new

  // Indicates the number of memory accesses to be performed
  rand int num_mem_reads;

  constraint num_mem_reads_c {
    num_mem_reads inside {[20 : 50]};
  }

  task body();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_mem_reads)
    do_rand_ops(num_mem_reads);
    read_digest_regs();
    dut_init();
    set_kmac_digest();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_mem_reads)
    do_rand_ops(num_mem_reads);
    read_digest_regs();
  endtask : body

endclass : rom_ctrl_smoke_vseq
