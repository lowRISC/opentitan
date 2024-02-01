// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test maximum ROM throughput with zero_delays=1
// It takes N+1 cycles to finish N read accesses.
class rom_ctrl_throughput_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_throughput_vseq)

  `uvm_object_new

  // Indicates the number of memory accesses to be performed
  rand int num_mem_reads;

  constraint num_mem_reads_c {
    num_mem_reads inside {[20 : 50]};
  }

  // Indicates the number of iterations
  rand int num_trans;

  constraint num_trans_c {
    num_trans inside {[1 : 10]};
  }

  task body();
    int num_cycles;
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_trans)
    for (int i = 0; i <= num_trans; i++) begin
      `uvm_info(`gfn, $sformatf("iterating %0d/%0d", i, num_trans), UVM_LOW)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_mem_reads)
      wait (cfg.rom_ctrl_vif  .pwrmgr_data.done == prim_mubi_pkg::MuBi4True);
      `DV_SPINWAIT_EXIT(
           // thread 1 to count cycles
           forever begin
             // Counting negedge to avoid one extra clock cycle count when d_valid id pulled down
             @(negedge cfg.clk_rst_vif.clk);
             num_cycles++;
           end,
           // thread 2 to do ROM OPs
           do_rand_ops(num_mem_reads, 1););

      `uvm_info(`gfn, $sformatf("num_cycles: %0d, num_mem_reads: %0d",num_cycles, num_mem_reads),
                UVM_MEDIUM)

      `DV_CHECK_EQ(num_cycles, num_mem_reads + 1);
      num_cycles = 0;
    end
  endtask : body

endclass : rom_ctrl_throughput_vseq
