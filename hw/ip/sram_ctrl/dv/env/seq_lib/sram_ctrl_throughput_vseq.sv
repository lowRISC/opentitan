// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test maximum sram throughput with zero_delays=1
// If no partial write is enabled, it takes N+1 cycles to finish N read/write accesses
// If there are M partial writes, it takes extra M*2 cycles
class sram_ctrl_throughput_vseq extends sram_ctrl_smoke_vseq;
  `uvm_object_utils(sram_ctrl_throughput_vseq)

  `uvm_object_new

  int num_partial_write;

  // Track the number of writes and reads and whether the most recent transaction
  // was a write. This is updated in get_rand_mask.
  int num_writes;
  int num_reads;
  int last_was_write;

  task body();
    // In order to have max throughput, don't drop a_valid
    cfg.m_tl_agent_cfgs[cfg.sram_ral_name].allow_a_valid_drop_wo_a_ready = 0;

    req_mem_init();
    if (init_w_readback) begin
      // Init the sequence with the SRAM readback feature enabled.
      csr_wr(.ptr(ral.readback), .value(MuBi4True));
    end

    // And wait for side_effects of ram_init to be done, since detection of the end is not very
    // accurate and memory transactions wll be blocked until init is completely done. The number
    // 20 below is not special, it is just a sensible guess.
    cfg.clk_rst_vif.wait_clks(20);

    for (int i = 0; i < num_trans; i++) begin
      int num_cycles = 0;

      num_partial_write = 0;

      num_writes = 0;
      num_reads = 0;
      last_was_write = 0;

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_ops)
      `uvm_info(`gfn, $sformatf("iteration: %0d, issuing %0d ops", i, num_ops), UVM_LOW)

      `DV_SPINWAIT_EXIT(
          // thread 1 to count cycles
          forever begin
            cfg.clk_rst_vif.wait_clks(1);
            num_cycles++;
          end,
          // thread 2 to do sram OPs
          do_rand_ops(.num_ops(num_ops),
                      .blocking(0));)

      `uvm_info(`gfn, $sformatf("num_cycles: %0d, num_ops: %0d, num_partial_write: %0d",
                                num_cycles, num_ops, num_partial_write), UVM_MEDIUM)
      if (init_w_readback) begin
        // In throughput_w_readback test, if the last operation was a write, subtract
        // one as the write already gets acknowledged over TLUL while the readback error
        // is still doing the readback of the written value.
        `DV_CHECK_EQ(num_cycles, num_writes * 3 + num_reads * 2 - last_was_write);
      end else begin
        `DV_CHECK_EQ(num_cycles, num_ops + 1 + num_partial_write * 2);
      end
    end
  endtask : body

  // override the function to count how many reads, writes, and partial writes are sent
  virtual function bit[bus_params_pkg::BUS_DBW-1:0] get_rand_mask(bit write);
    bit [bus_params_pkg::BUS_DBW-1:0] mask = super.get_rand_mask(write);

    if (write && mask != '1) num_partial_write++;

    // Keep track of number of writes and reads for readback test.
    if (write) begin
      num_writes++;
      last_was_write = 1;
    end else begin
      num_reads++;
      last_was_write = 0;
    end

    return mask;
  endfunction

endclass : sram_ctrl_throughput_vseq
