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
    // Initialize memory at the beginning of reset since the DUT can come out of reset before this
    // task completes (due to the second RAL clk_rst_if)
    rom_ctrl_mem_init();
    super.apply_reset(kind);
  endtask

  // Task to build a random rom in memory
  virtual task rom_ctrl_mem_init();
    // randomize the memory contents
    cfg.mem_bkdr_util_h.randomize_mem();
  endtask

  // Task to perform `num_ops` fully randomized memory transactions.
  virtual task do_rand_ops(int num_ops);
    addr_range_t loc_mem_range[$] = cfg.ral_models["rom_ctrl_rom_reg_block"].mem_ranges;

    bit [TL_DW-1:0] data;
    bit [TL_AW-1:0] addr;
    bit             write;
    int             mem_idx;

    repeat (num_ops) begin
      bit completed, saw_err;

      int mem_idx = $urandom_range(0, loc_mem_range.size - 1);
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(addr,
          addr inside {[loc_mem_range[mem_idx].start_addr :
                        loc_mem_range[mem_idx].end_addr]};)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(write, !do_rom_error_req -> write == 1'b0;)

      tl_access_w_abort(.addr(addr),
                        .data(data),
                        .completed(completed),
                        .saw_err(saw_err),
                        .mask(get_rand_contiguous_mask('1)),
                        .write(write),
                        .blocking(1'b0),
                        .check_rsp(1'b0),
                        .tl_sequencer_h(p_sequencer.tl_sequencer_hs["rom_ctrl_rom_reg_block"]),
                        .req_abort_pct(do_rom_error_req ? 50 : 0));
    end
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  virtual task read_digest_regs();
    bit [TL_DW-1:0] rdata;
    for (int i = 0; i < DIGEST_SIZE / TL_DW; i++) begin
      string digest_name = $sformatf("digest_%0d", i);
      uvm_reg csr = ral.get_reg_by_name(digest_name);
      csr_rd(.ptr(csr), .value(rdata));
    end
    for (int i = 0; i < DIGEST_SIZE / TL_DW; i++) begin
      string digest_name = $sformatf("exp_digest_%0d", i);
      uvm_reg csr = ral.get_reg_by_name(digest_name);
      csr_rd(.ptr(csr), .value(rdata));
    end
  endtask

endclass : rom_ctrl_base_vseq
