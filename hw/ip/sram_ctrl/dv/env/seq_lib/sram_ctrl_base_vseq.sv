// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_base_vseq #(parameter int AddrWidth = `SRAM_ADDR_WIDTH) extends cip_base_vseq #(
    .RAL_T               (sram_ctrl_regs_reg_block),
    .CFG_T               (sram_ctrl_env_cfg#(AddrWidth)),
    .COV_T               (sram_ctrl_env_cov#(AddrWidth)),
    .VIRTUAL_SEQUENCER_T (sram_ctrl_virtual_sequencer#(AddrWidth))
  );
  `uvm_object_param_utils(sram_ctrl_base_vseq#(AddrWidth))
  `uvm_object_new

  rand mubi4_t readback_en;

  // various knobs to enable certain routines
  bit readback_running = 0;

  bit do_readback_en = 0;

  bit do_sram_ctrl_init = 1'b1;

  bit stress_pipeline = 1'b0;

  int partial_access_pct = 10;

  constraint readback_en_c {
    soft readback_en inside {MuBi4True, MuBi4False};
  }

  virtual task pre_start();
    super.pre_start();
    void'($value$plusargs("partial_access_pct=%0d", partial_access_pct));
    `DV_CHECK_LE(partial_access_pct, 100)
    // Wait for ram initialization to be done, since it blocks memory accesses.
    `DV_WAIT(cfg.in_init == 1'b0, "Timed out waiting for initialization done")
    // Make sure that the sram_readback_en task only runs once during the test.
    // This is important to make sure that only one sram_readback_en task sets
    // or unsets the readback enable CSR.
    if (!uvm_config_db #(bit)::get(get_sequencer(), "*", "readback_running",
        readback_running)) begin
      uvm_config_db #(bit)::set(null, "*", "readback_running", readback_running);
    end
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_sram_ctrl_init) sram_ctrl_init();
    if (!readback_running && do_readback_en) sram_readback_en();
  endtask

  // Enable readback feature only for non-throughput and non-sec_cm tests. The
  // readback feature is randomly initialized to on/off at the start of the test
  // and randomly switched during the tests.
  // TODO(#23321) Adapt the troughput tests to take the delay caused by the
  // readback feature into account.
  virtual protected task sram_readback_en();
    readback_running = 1;
    if (uvm_re_match("*throughput*", get_type_name()) &&
        uvm_re_match("*sec_cm*", get_type_name()) &&
        uvm_re_match("*readback_err*", get_type_name()) &&
        uvm_re_match("*throughput*", common_seq_type) &&
        uvm_re_match("*sec_cm*", common_seq_type) &&
        uvm_re_match("*readback_err*", common_seq_type)) begin
      // Configure the SRAM TLUL agent to wait at least 2 cycles before dropping
      // a request.
      cfg.m_tl_agent_cfgs[cfg.sram_ral_name].a_valid_len_min = 2;
      // Init the readback enable randomly to true or false.
      csr_utils_pkg::wait_no_outstanding_access();
      csr_wr(.ptr(ral.readback), .value(readback_en));
      // Randomly toggle the readback enable during the test.
      fork
        begin
          forever begin
            cfg.clk_rst_vif.wait_clks($urandom_range(10, 10_000));
            std::randomize(readback_en) with {
              readback_en inside {MuBi4True, MuBi4False};};
            // Wait until cfg.in_key_req == 0 as writing to the readback CSR
            // issues a TL-UL transaction to the register interface of the
            // module, which triggers the following assertion inside
            // the sram_ctrl_scoreboard:
            // `DV_CHECK_EQ(cfg.in_key_req, 0, "No item is accepted during key req")
            `DV_SPINWAIT(wait (cfg.in_key_req == 0);)
            csr_utils_pkg::wait_no_outstanding_access();
            csr_wr(.ptr(ral.readback), .value(readback_en));
            `uvm_info(`gfn, "Update READBACK Value", UVM_MEDIUM)
          end
        end
      join_none
    end
  endtask : sram_readback_en

  virtual task apply_reset(string kind = "HARD");
    cfg.lc_vif.init();
    cfg.exec_vif.init();
    fork
      super.apply_reset(kind);
      if (kind == "HARD") begin
        cfg.otp_clk_rst_vif.apply_reset();
      end
    join
  endtask

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.lc_vif.init();
    cfg.otp_clk_rst_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(cfg.otp_clk_rst_vif.clk_period_ps);
    cfg.otp_clk_rst_vif.drive_rst_pin(1);
    cfg.exec_vif.init();
  endtask

  virtual task dut_shutdown();
    // check for pending sram_ctrl operations and wait for them to complete
  endtask

  // setup basic sram_ctrl features
  virtual task sram_ctrl_init();
    req_mem_init();
  endtask

  // Increase the number of cycles to wait for no outstanding accesses, since it is hard
  // to sequence all invocations of pre_start, and that can trigger ram init which blocks
  // accesses for a long time. The RAM has 32K words, and it updates one per cycle, so
  // 50,000 cycles should be okay.
  virtual function int wait_cycles_with_no_outstanding_accesses();
    return 50_000;
  endfunction

  // Request a memory init, and  wait for it to complete. This is a problematic task since
  // it would be better to set the in_init and in_key_req in either this place or in
  // process_tl_access, except in cip sequences the will not be called. If the scoreboard
  // is enabled it is more accurate to let it set the in_init and in_key_req flags.
  virtual task req_mem_init(bit wait_done = 1);
    // Use csr_wr rather than csr_update, because we change this reg type to RO in RAL when
    // ctrl_regwen is clear. csr_update won't issue a write to this CSR
    csr_wr(.ptr(ral.ctrl), .value('b11));

    // if ctrl_regwen is off, init won't start
    if (!`gmv(ral.ctrl_regwen)) begin
      `uvm_info(`gfn, "regwen blocks mem_init", UVM_MEDIUM)
      return;
    end

    // The following flags are set in the process_tl_access when the scoreboard is enabled.
    if (!cfg.en_scb) begin
      cfg.in_init = 1'b1;
      `uvm_info(`gfn, "In req_mem_init setting in_key_req = 1", UVM_MEDIUM)
      cfg.in_key_req = 1'b1;
    end
    if (wait_done) begin
      `DV_WAIT(cfg.in_init == 1'b0, "Timed out waiting for initialization done")
      cfg.disable_d_user_data_intg_check_for_passthru_mem = 0;
    end
  endtask

  // Request a new scrambling key from the OTP interface.
  //
  // Will trigger a request to the KDI push_pull agent.
  virtual task req_scr_key(bit wait_valid = 1);
    // If we only do scrambling without re-initializing the mem, data intg will be wrong
    // since it's data intg passthru mem, it doesn't matter, just don't check it.
    cfg.disable_d_user_data_intg_check_for_passthru_mem = 1;
    ral.ctrl.renew_scr_key.set(1);
    csr_update(.csr(ral.ctrl));
    // The following flags are set in process_tl_access when the scoreboard is enabled.
    if (!cfg.en_scb) begin
      `uvm_info(`gfn, "In req_src_init setting in_key_req = 1", UVM_MEDIUM)
      cfg.in_key_req = 1'b1;
    end
    if (wait_valid) begin
      `DV_WAIT(cfg.in_key_req == 1'b0, "Timed out waiting for key request done")
      cfg.disable_d_user_data_intg_check_for_passthru_mem = 0;
    end
  endtask

  // Task to perform a single SRAM read at the specified location
  virtual task do_single_read(input bit [TL_AW-1:0]    addr,
                              input bit [TL_DBW-1:0]   mask         = get_rand_mask(.write(0)),
                              input bit                blocking     = $urandom_range(0, 1),
                              input bit                check_rdata  = 0,
                              input bit [TL_DW-1:0]    exp_rdata    = '0,
                              input mubi4_t            instr_type   = MuBi4False,
                              output logic [TL_DW-1:0] rdata);
    `uvm_info(`gfn, $sformatf("do_single_read addr 0x%x", addr), UVM_HIGH)
    tl_access(.addr(addr),
              .data(rdata),
              .mask(mask),
              .write(1'b0),
              .blocking(blocking),
              .check_exp_data(check_rdata),
              .exp_data(exp_rdata),
              .compare_mask(mask),
              .instr_type(instr_type),
              .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.sram_ral_name]));
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  // Task to perform a single SRAM write at the specified location
  virtual task do_single_write(bit [TL_AW-1:0]  addr,
                               bit [TL_DW-1:0]  data,
                               bit [TL_DBW-1:0] mask        = get_rand_mask(.write(1)),
                               bit              blocking    = $urandom_range(0, 1),
                               mubi4_t          instr_type  = MuBi4False);
    `uvm_info(`gfn, $sformatf("do_single_write addr 0x%x, data 0x%x", addr, data), UVM_HIGH)
    tl_access(.addr(addr),
              .data(data),
              .mask(mask),
              .write(1'b1),
              .blocking(blocking),
              .instr_type(instr_type),
              .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.sram_ral_name]));
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  // This task is designed to kick off `num_stress_ops` back to back memory transactions
  // to the same address, to stress the SRAM pipelining implementation
  virtual task do_stress_ops(bit [TL_AW-1:0] addr,
                             int num_stress_ops,
                             bit en_ifetch = 0);
    bit [TL_DW-1:0] data;
    mubi4_t instr_type;

    repeat (num_stress_ops) begin
      bit write = $urandom_range(0, 1);
      if (cfg.stop_transaction_generators()) break;
      // fully randomize data
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)

      // never send InstrType transactions unless en_ifetch is enabled
      if (en_ifetch) instr_type = get_rand_mubi4_val();
      else           instr_type = MuBi4False;

      tl_access(.addr(addr),
                .data(data),
                .mask(get_rand_mask(write)),
                .write(write),
                .check_rsp(!en_ifetch),
                .blocking(1'b0),
                .instr_type(instr_type),
                .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.sram_ral_name]));
    end
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  // Task to perform `num_ops` fully randomized memory transactions.
  //
  // Includes capability to abort transactions after several cycles if no response
  // is seen from the SRAM.
  // This is useful for when we are testing memory operations during terminal states
  // (such as during LC escalations or parity errors), which are expected to not respond at all.
  //
  // not_use_last_addr is used to constrain the address is not equal to max address.
  virtual task do_rand_ops(int num_ops,
                           bit blocking  = $urandom_range(0, 1),
                           bit abort     = 0,
                           bit en_ifetch = 0,
                           bit wait_complete = 1,
                           bit not_use_last_addr = 0,
                           bit exp_err_rsp = 0,
                           bit check_rsp = 1);
    bit [TL_DW-1:0] data;
    bit [TL_AW-1:0] addr;
    mubi4_t instr_type;
    bit [TL_AW-1:0] sram_addr_mask = cfg.ral_models[cfg.sram_ral_name].get_addr_mask();
    bit [TL_AW-1:0] max_offset = {sram_addr_mask[TL_AW-1:2], 2'd0};

    repeat (num_ops) begin
      bit completed, saw_err;
      bit write = $urandom_range(0, 1);

      if (cfg.stop_transaction_generators()) break;

      // full randomize addr and data
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(addr,
                                         if (not_use_last_addr) {
                                           (addr & sram_addr_mask) < max_offset;
                                         })

      // never send InstrType transactions unless en_ifetch is enabled
      if (en_ifetch) instr_type = get_rand_mubi4_val();
      else           instr_type = MuBi4False;

      tl_access_w_abort(.addr(addr),
                        .data(data),
                        .completed(completed),
                        .saw_err(saw_err),
                        .mask(get_rand_mask(write)),
                        .write(write),
                        .blocking(blocking),
                        .check_rsp(!en_ifetch & check_rsp),
                        .exp_err_rsp(exp_err_rsp),
                        .instr_type(instr_type),
                        .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.sram_ral_name]),
                        .req_abort_pct((abort) ? 100 : 0));
    end
    if (wait_complete) csr_utils_pkg::wait_no_outstanding_access();
  endtask

  // the input write argument will be used in extended test where this function is overridden
  virtual function bit[bus_params_pkg::BUS_DBW-1:0] get_rand_mask(bit write);
    bit [bus_params_pkg::BUS_DBW-1:0] mask;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask,
        // mask to be contiguous
        // if one bit is set, 'b1 ^ 'b10 <= 2
        // if 2 bits are set, 'b11 ^ 'b110 <= 2
        //     non-contiguous cases: 'b101 ^ 'b1010 = 4, 'b1001 ^ 'b0010 = 3
        // if 3 bits are set, 'b111 ^ 'b1110 <= 2
        //     non-contiguous cases: 'b1101 ^ 'b1010 = 3, 'b1011 ^ 'b0110 = 3
        $countones(mask ^ {mask[bus_params_pkg::BUS_DBW-2:0], 1'b0}) <= 2;
        mask dist {'1 :/ 100 - partial_access_pct,
                   [0 : '1 - 1] :/ partial_access_pct};)
    return mask;
  endfunction

endclass : sram_ctrl_base_vseq
