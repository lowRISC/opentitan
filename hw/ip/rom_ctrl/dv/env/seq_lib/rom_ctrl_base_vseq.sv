// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (rom_ctrl_regs_reg_block),
    .CFG_T               (rom_ctrl_env_cfg),
    .COV_T               (rom_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (rom_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(rom_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_rom_ctrl_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_rom_ctrl_init) rom_ctrl_init();
  endtask

  virtual task dut_shutdown();
    // check for pending rom_ctrl operations and wait for them to complete
    // TODO
  endtask

  // setup basic rom_ctrl features
  virtual task rom_ctrl_init();
    // Disable intr test since no interrupts
    do_clear_all_interrupts = 1'b0;
    // Initialize memory
    rom_ctrl_mem_init();
  endtask

  // Task to build a random rom in memory
  virtual task rom_ctrl_mem_init();
    // randomize the memory contents
    cfg.mem_bkdr_vif.randomize_mem();
  endtask

  // Task to perform `num_ops` fully randomized memory transactions.
  virtual task do_rand_ops(int num_ops);
    uvm_status_e status;

    bit [TL_DW-1:0] data;
    bit [TL_AW-1:0] addr;
    repeat (num_ops) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      `DV_CHECK_STD_RANDOMIZE_FATAL(addr)

      tl_access_w_abort(.addr(addr),
                        .data(data),
                        .status(status),
                        .mask(get_rand_contiguous_mask()),
                        .write(1'b0),
                        .blocking(1'b0),
                        .tl_sequencer_h(p_sequencer.rom_tl_sequencer_h),
                        .req_abort_pct(0));
    end
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

endclass : rom_ctrl_base_vseq
