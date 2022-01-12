// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test maximum sram throughput with zero_delays=1
// If no partial write is enabled, it takes N+1 cycles to finish N read/write accesses
// If there are M partial writes, it takes extra M*2 cycles
class sram_ctrl_throughput_vseq extends sram_ctrl_smoke_vseq;
  `uvm_object_utils(sram_ctrl_throughput_vseq)

  `uvm_object_new

  int num_partial_write;

  task body();
    // In order to have max throughput, don't drop a_valid
    cfg.m_tl_agent_cfgs[cfg.sram_ral_name].allow_a_valid_drop_wo_a_ready = 0;

    req_mem_init();
    for (int i = 0; i < num_trans; i++) begin
      int num_cycles;

      num_partial_write = 0;
      `uvm_info(`gfn, $sformatf("iteration: %0d", i), UVM_LOW)

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_ops)

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

      `DV_CHECK_EQ(num_cycles, num_ops + 1 + num_partial_write * 2);
    end
  endtask : body

  // override the function to count how many partial writes are sent
  virtual function bit[bus_params_pkg::BUS_DBW-1:0] get_rand_mask(bit write);
    bit [bus_params_pkg::BUS_DBW-1:0] mask = super.get_rand_mask(write);

    if (write && mask != '1) num_partial_write++;
    return mask;
  endfunction

endclass : sram_ctrl_throughput_vseq
