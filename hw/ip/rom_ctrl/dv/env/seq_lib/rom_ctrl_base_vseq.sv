// Copyright lowRISC contributors (OpenTitan project).
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
    for (int i = 0; i < ROM_SIZE_WORDS; i++) begin
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
    addr_range_t loc_mem_range[$] = cfg.ral_models["rom_ctrl_prim_reg_block"].mem_ranges;

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
                        .tl_sequencer_h(p_sequencer.tl_sequencer_hs["rom_ctrl_prim_reg_block"]),
                        .req_abort_pct(do_rom_error_req ? 50 : 0),
                        .tl_access_timeout_ns(cfg.tl_access_timeout_ns));
    end
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  // Read the digest[i] registers (computed by kmac) and the exp_digest[i] registers (which rom_ctrl
  // read from the top of the ROM). Check these registers all have their expected values.
  virtual task read_digest_regs();
    uvm_status_e status;
    for (int i = 0; i < DIGEST_SIZE / TL_DW; i++) begin
      ral.digest[i].mirror(.status(status), .check(UVM_CHECK));
      `DV_CHECK_EQ(status, UVM_IS_OK)
    end
    for (int i = 0; i < DIGEST_SIZE / TL_DW; i++) begin
      ral.exp_digest[i].mirror(.status(status), .check(UVM_CHECK));
      `DV_CHECK_EQ(status, UVM_IS_OK)
    end
  endtask

  // Pull the expected digest value from the top of rom
  virtual function bit [DIGEST_SIZE-1:0] get_expected_digest();
    bit [DIGEST_SIZE-1:0]    digest;
    bit [`ROM_BYTE_ADDR_WIDTH-1:0] dig_addr;
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

  // Overrides tl_access in cip_base_vseq to add custom timeout. Timeout overriden to
  // cfg.tl_access_timeout_ns (40ms)
  // The ROM takes a while to be read and otherwise some tests may timeout when using
  // default timeout.
  virtual task tl_access(input bit [TL_AW-1:0]  addr,
                         input bit              write,
                         inout bit [TL_DW-1:0]  data,
                         input uint             tl_access_timeout_ns = cfg.tl_access_timeout_ns,
                         input bit [TL_DBW-1:0] mask = '1,
                         input bit              check_rsp = 1'b1,
                         input bit              exp_err_rsp = 1'b0,
                         input bit [TL_DW-1:0]  exp_data = 0,
                         input bit [TL_DW-1:0]  compare_mask = '1,
                         input bit              check_exp_data = 1'b0,
                         input bit              blocking = csr_utils_pkg::default_csr_blocking,
                         input mubi4_t          instr_type = MuBi4False,
                         tl_sequencer           tl_sequencer_h = p_sequencer.tl_sequencer_h,
                         input tl_intg_err_e    tl_intg_err_type = TlIntgErrNone);

    super.tl_access(.addr(addr), .write(write), .data(data),
                    .tl_access_timeout_ns(tl_access_timeout_ns),
                    .mask(mask), .check_rsp(check_rsp), .exp_err_rsp(exp_err_rsp),
                    .compare_mask(compare_mask), .check_exp_data(check_exp_data),
                    .blocking(blocking), .instr_type(instr_type), .tl_sequencer_h(tl_sequencer_h),
                    .tl_intg_err_type(tl_intg_err_type));
  endtask

  // Overrides tl_access_w_abort in cip_base_vseq to add custom timeout. Timeout overriden to
  // cfg.tl_access_timeout_ns (40ms)
  // The ROM takes a while to be read and otherwise some tests may timeout when using
  // default timeout.
  virtual task tl_access_w_abort(
      input bit [TL_AW-1:0]  addr,
      input bit              write,
      inout bit [TL_DW-1:0]  data,
      output bit             completed,
      output bit             saw_err,
      input uint             tl_access_timeout_ns = cfg.tl_access_timeout_ns,
      input bit [TL_DBW-1:0] mask = '1,
      input bit              check_rsp = 1'b1,
      input bit              exp_err_rsp = 1'b0,
      input bit [TL_DW-1:0]  exp_data = 0,
      input bit [TL_DW-1:0]  compare_mask = '1,
      input bit              check_exp_data = 1'b0,
      input bit              blocking = csr_utils_pkg::default_csr_blocking,
      input mubi4_t          instr_type = MuBi4False,
      tl_sequencer           tl_sequencer_h = p_sequencer.tl_sequencer_h,
      input tl_intg_err_e    tl_intg_err_type = TlIntgErrNone,
      input int              req_abort_pct = 0);


    super.tl_access_w_abort(.addr(addr), .write(write), .data(data), .completed(completed),
                            .saw_err(saw_err), .tl_access_timeout_ns(tl_access_timeout_ns),
                            .mask(mask), .check_rsp(check_rsp), .exp_err_rsp(exp_err_rsp),
                            .exp_data(exp_data), .compare_mask(compare_mask),
                            .check_exp_data(check_exp_data), .blocking(blocking),
                            .instr_type(instr_type), .tl_sequencer_h(tl_sequencer_h),
                            .tl_intg_err_type(tl_intg_err_type), .req_abort_pct(req_abort_pct));
  endtask



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

  // Wait for a fatal alert to be raised
  //
  // We expect the FATAL_ALERT_CAUSE register to contain 32'd1, which means that the checker_error
  // field is true, but the integrity_error field is false.
  task wait_for_fatal_alert(bit check_fsm_state = 1'b1,
                            int max_delay = 10000,
                            int max_wait_cycle = 1000);
    uvm_reg_data_t act_val;
    cfg.scoreboard.set_exp_alert("fatal", .is_fatal(1'b1), .max_delay(max_delay));

    fork
      begin
        void'(ral.fatal_alert_cause.predict(.value(32'd1), .kind(UVM_PREDICT_READ), .be(4'hF)));
        wait_alert_trigger ("fatal", .max_wait_cycle(1000), .wait_complete(1));
        csr_utils_pkg::csr_rd(.ptr(ral.fatal_alert_cause), .value(act_val), .check(UVM_CHECK));
      end
      begin
        repeat(3) wait_alert_trigger ("fatal", .max_wait_cycle(max_wait_cycle), .wait_complete(1));
      end
    join

    if (check_fsm_state) begin
      string alert_o_path = "tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.alert_o";
      string state_q_path = "tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.state_q";
      bit    rdata_alert;
      bit [$bits(rom_ctrl_pkg::fsm_state_e)-1:0] rdata_state;
      `DV_CHECK(uvm_hdl_read(alert_o_path, rdata_alert))
      `DV_CHECK_EQ(rdata_alert, 1)
      `DV_CHECK(uvm_hdl_read(state_q_path, rdata_state))
      `DV_CHECK_EQ(rdata_state, rom_ctrl_pkg::Invalid)
    end
  endtask: wait_for_fatal_alert

endclass : rom_ctrl_base_vseq
