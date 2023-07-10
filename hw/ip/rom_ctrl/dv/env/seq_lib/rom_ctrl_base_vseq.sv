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

  virtual task apply_reset(string kind = "HARD");
    // Initialize memory at the beginning of reset since the DUT can come out of reset before this
    // task completes (due to the second RAL clk_rst_if)
    rom_ctrl_mem_init();
    super.apply_reset(kind);
  endtask

  // Task to build a random rom in memory
  virtual task rom_ctrl_mem_init();
    bit [31:0] rnd_data;

    // Randomize the memory contents.
    //
    // We can't just use the mem_bkdr_util randomize_mem function because that doesn't obey the
    // scrambling key. This wouldn't be a problem (the memory is supposed to be random!), except
    // that we also need to pick ECC values that match.
    for (int i = 0; i < rom_ctrl_reg_pkg::ROM_CTRL_ROM_SIZE / 4; i++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(rnd_data)
      cfg.mem_bkdr_util_h.rom_encrypt_write32_integ(i * 4,
                                                    rnd_data,
                                                    RND_CNST_SCR_KEY,
                                                    RND_CNST_SCR_NONCE,
                                                    1'b1);
    end
  endtask

  // Task to perform `num_ops` fully randomized memory transactions.
  virtual task do_rand_ops(int num_ops, bit read_only = 0);
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
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(write, !do_rom_error_req -> write == 1'b0;
                                         read_only -> write == 1'b0;)

      tl_access_w_abort(.addr(addr),
                        .data(data),
                        .completed(completed),
                        .saw_err(saw_err),
                        .mask(get_rand_contiguous_mask('1)),
                        .write(write),
                        .blocking(1'b0),
                        .check_rsp(1'b0),
                        .tl_sequencer_h(p_sequencer.tl_sequencer_hs["rom_ctrl_rom_reg_block"]),
                        .req_abort_pct(do_rom_error_req ? 50 : 0),
                        .tl_access_timeout_ns(cfg.tl_access_timeout_ns));
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

  // Pull the expected digest value from the top of rom
  virtual function bit [DIGEST_SIZE-1:0] get_expected_digest();
    bit [DIGEST_SIZE-1:0]    digest;
    bit [rom_ctrl_reg_pkg::RomAw-1:0] dig_addr;
    // Get the digest from rom
    // The digest is the top 8 words in memory (unscrambled)
    dig_addr = MAX_CHECK_ADDR;
    for (int i = 0; i < DIGEST_SIZE / TL_DW; i++) begin
      bit [ROM_MEM_W-1:0] mem_data = cfg.mem_bkdr_util_h.rom_encrypt_read32(
          dig_addr, RND_CNST_SCR_KEY, RND_CNST_SCR_NONCE, 1'b0);
      digest[i*TL_DW+:TL_DW] = mem_data[TL_DW-1:0];
      dig_addr += (TL_DW / 8);
    end
    return digest;
  endfunction

  // Set KMAC digest_share0 with ROM digest value and digest_share1 with 0
  virtual function void set_kmac_digest();
    bit [DIGEST_SIZE-1:0]  expected_digest;
    bit [kmac_pkg::AppDigestW-1:0] share0;
    kmac_pkg::rsp_digest_t rsp_digest_h;
    expected_digest = get_expected_digest();
    `DV_CHECK_STD_RANDOMIZE_FATAL(share0)
    rsp_digest_h.digest_share0 = share0;
    rsp_digest_h.digest_share1 = rsp_digest_h.digest_share0 ^ expected_digest;
    cfg.m_kmac_agent_cfg.add_user_digest_share(rsp_digest_h);
  endfunction

endclass : rom_ctrl_base_vseq
