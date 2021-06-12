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
  bit do_rom_error_req = 1'b0;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    // Disable intr test since no interrupts
    do_clear_all_interrupts = 1'b0;
  endtask

  virtual task dut_shutdown();
    // check for pending rom_ctrl operations and wait for them to complete
    // TODO
  endtask

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset(kind);
    // Initialize memory
    rom_ctrl_mem_init();
  endtask

  // Task to build a random rom in memory
  virtual task rom_ctrl_mem_init();
    // randomize the memory contents
    cfg.mem_bkdr_util_h.randomize_mem();
  endtask

  // Task to perform `num_ops` fully randomized memory transactions.
  virtual task do_rand_ops(int num_ops);
    uvm_status_e status;

    bit [TL_DW-1:0] data;
    bit [TL_AW-1:0] addr;
    bit             write;
    repeat (num_ops) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      `DV_CHECK_STD_RANDOMIZE_FATAL(addr)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(write, !do_rom_error_req -> write == 1'b0;)

      tl_access_w_abort(.addr(addr),
                        .data(data),
                        .status(status),
                        .mask(get_rand_contiguous_mask('1)),
                        .write(write),
                        .blocking(1'b0),
                        .check_rsp(1'b0),
                        .tl_sequencer_h(p_sequencer.rom_tl_sequencer_h),
                        .req_abort_pct(do_rom_error_req ? 50 : 0));
    end
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  virtual task read_digest_regs();
    bit [TL_DW-1:0] rdata;
    for (int i = 0; i < kmac_pkg::AppDigestW / TL_DW; i++) begin
      string digest_name = $sformatf("digest_%0d", i);
      uvm_reg csr = ral.get_reg_by_name(digest_name);
      csr_rd(.ptr(csr), .value(rdata));
    end
    for (int i = 0; i < kmac_pkg::AppDigestW / TL_DW; i++) begin
      string digest_name = $sformatf("exp_digest_%0d", i);
      uvm_reg csr = ral.get_reg_by_name(digest_name);
      csr_rd(.ptr(csr), .value(rdata));
    end
  endtask

endclass : rom_ctrl_base_vseq
