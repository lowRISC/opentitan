// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Run back-to-back ROM accesses with zero_delays=1 in order to test throughput
//
// Each ROM access takes two cycles (one for the A channel request, then one for the D channel
// response). Because these operations can run back-to-back with both channels in use, we expect N
// reads to take N+1 cycles.

class rom_ctrl_throughput_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_throughput_vseq)

  // Indicates the number of memory accesses to be performed
  rand int num_mem_reads;

  extern function new(string name="");
  extern task body();

  extern constraint num_mem_reads_c;
endclass : rom_ctrl_throughput_vseq

function rom_ctrl_throughput_vseq::new(string name="");
  super.new(name);
endfunction

task rom_ctrl_throughput_vseq::body();
  // Expected minimum and maximum time for the reads
  int unsigned min_num_cycles, max_num_cycles;

  // The actual time that the reads have taken
  int num_cycles;

  wait (cfg.rom_ctrl_vif.pwrmgr_data_o_i.done == prim_mubi_pkg::MuBi4True);

  `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_mem_reads)
  `uvm_info(get_full_name(), $sformatf("Measuring time for %0d ROM reads", num_mem_reads), UVM_LOW)

  // We expect each memory read to take two cycles, but the D channel transaction for read N can
  // overlap with the A channel transaction of read N+1. As such, we expect K transactions to take
  // K+1 cycles.
  //
  // However, there's the possibility of measuring one extra cycle if tl_host_driver wasn't just
  // driving a transaction, giving a maximum of K+2 cycles.
  min_num_cycles = num_mem_reads + 1;
  max_num_cycles = min_num_cycles + 1;

  fork begin : isolation_fork
    fork
      do_rand_ops(num_mem_reads, 1);
      forever begin
        // Count negative edges to avoid racing with start/end of do_rand_ops.
        @(negedge cfg.clk_rst_vif.clk);
        num_cycles++;
      end
    join_any
    disable fork;
  end join

  if (num_cycles < min_num_cycles || max_num_cycles < num_cycles) begin
    `uvm_error(get_full_name(),
               $sformatf({"Reading %0d words from memory was measured to take %0d cycles, ",
                          "but was expected to take between %0d and %0d cycles."},
                         num_mem_reads, num_cycles, min_num_cycles, max_num_cycles))
  end
endtask : body

constraint rom_ctrl_throughput_vseq::num_mem_reads_c {
  num_mem_reads inside {[200 : 500]};
}
