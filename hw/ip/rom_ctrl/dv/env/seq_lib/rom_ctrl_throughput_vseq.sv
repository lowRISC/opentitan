// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Run back-to-back ROM accesses with zero_delays=1 in order to test throughput
//
// Each ROM access takes two cycles (one for the A channel request, then one for the D channel
// response). Because these operations can run back-to-back with both channels in use, the highest
// possible throughput is that N reads take N+1 cycles. (These will be counted as N+2 cycles below
// because of timing in the TL agent, which is explained in detail in the body).

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
  int num_cycles;

  wait (cfg.rom_ctrl_vif.pwrmgr_data.done == prim_mubi_pkg::MuBi4True);

  `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_mem_reads)
  `uvm_info(get_full_name(), $sformatf("Measuring time for %0d ROM reads", num_mem_reads), UVM_LOW)

  // The timing in tl_host_driver depends on whether it is handling back-to-back operations or
  // whether there has been a gap. Because this virtual sequence expects to be the only thing
  // accessing the interface, we can make sure which timing to expect by inserting a 1-cycle gap
  // here.
  cfg.clk_rst_vif.wait_clks(1);

  `DV_SPINWAIT_EXIT(
       // thread 1 to count cycles
       forever begin
         // Counting negedge to avoid one extra clock cycle count when d_valid id pulled down
         @(negedge cfg.clk_rst_vif.clk);
         num_cycles++;
       end,
       // thread 2 to do ROM OPs
       do_rand_ops(num_mem_reads, 1););

  // We expect num_mem_reads operations to take 1 + num_mem_reads + 1 cycles, where the first
  // cycle is taken by the driver lining up with the posedge of the clock again (when it got the
  // first item after a gap), then the following num_mem_reads+1 cycles are taken by overlapping
  // each of the num_mem_reads operations by a cycle each.
  if (num_cycles != num_mem_reads + 2) begin
    `uvm_error(get_full_name(),
               $sformatf({"Reading %0d words from memory was measured to take %0d cycles, ",
                          "but was expected to take 1+%0d+1 = %0d."},
                         num_mem_reads, num_cycles, num_mem_reads, num_mem_reads + 2))
  end
endtask : body

constraint rom_ctrl_throughput_vseq::num_mem_reads_c {
  num_mem_reads inside {[200 : 500]};
}
