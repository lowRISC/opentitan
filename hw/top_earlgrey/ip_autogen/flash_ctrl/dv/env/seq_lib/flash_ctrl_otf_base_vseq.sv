// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is base class for on the fly mode test sequence.
// On the fly mode test checks data integrity per transaction (program or read),
// and doesn't rely on reference memory model in the test bench.
class flash_ctrl_otf_base_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_otf_base_vseq)
  `uvm_object_new

  // The maximum number of attempts to get an address that has not been previously written.
  localparam int MaxProgAttempts = 16;

  // Used for tracing programmed data
  bit [15:0] global_pat_cnt = 16'hA000;

  // Double bit err is created
  bit        global_derr_is_set = 0;

  // Trace host read ountstanding
  int        d_cnt1, d_cnt2;

  // Number of controller transactions per a single task
  // Min: 1 Max:32
  rand int  ctrl_data_num;
  rand int  ctrl_info_num;
  rand int  ctrl_num;

  rand bit  is_addr_odd;
  rand int  fractions;

  // flash op
  // WIP. not all field is valid.
  rand flash_op_t rand_op;

  // Permission to access special partition
  rand bit [2:0] allow_spec_info_acc;
  rand bit       all_entry_en;

  // scramble and ecc config mode
  rand otf_cfg_mode_e scr_ecc_cfg;

  rand flash_mp_region_cfg_t rand_regions[MpRegions];
  rand flash_bank_mp_info_page_cfg_t rand_info[NumBanks][InfoTypes][$];
  flash_mem_init_e otf_flash_init = FlashMemInitEccMode;

  constraint all_ent_c {
    solve all_entry_en before rand_regions, rand_info;
    if (cfg.en_always_any) all_entry_en == 1;
    else all_entry_en dist { 1 := 1, 0 := 4};
  }
  constraint scr_ecc_c {
    scr_ecc_cfg dist { OTFCfgRand := 5, OTFCfgTrue := 4};
  }
  constraint rand_regions_c {
    foreach (rand_regions[i]) {
      if (all_entry_en) rand_regions[i].en == MuBi4True;
      rand_regions[i].start_page dist {
        0                       := 1,
        [1 : FlashNumPages - 2] :/ 8,
        FlashNumPages - 1       := 1
      };
      rand_regions[i].num_pages inside {[1 : FlashNumPages - rand_regions[i].start_page]};
      rand_regions[i].num_pages <= 32;
      rand_regions[i].scramble_en dist { MuBi4True := 4, MuBi4False := 1};
      rand_regions[i].ecc_en dist { MuBi4True := 4, MuBi4False := 1};
    }
  }
  constraint rand_info_c {
    foreach (rand_info[i, j]) {
      rand_info[i][j].size() == InfoTypeSize[j];
      foreach (rand_info[i][j][k]) {
        if (all_entry_en) rand_info[i][j][k].en == MuBi4True;
        rand_info[i][j][k].en dist { MuBi4True := 4, MuBi4False :=1};
        if (cfg.en_always_read) rand_info[i][j][k].read_en == MuBi4True;
        rand_info[i][j][k].scramble_en dist { MuBi4True := 4, MuBi4False :=1};
        rand_info[i][j][k].ecc_en dist { MuBi4True := 4, MuBi4False :=1};
      }
    }
  }
  constraint ctrl_data_num_c {
    ctrl_data_num dist { CtrlTransMin := 2, [2:31] :/ 1, CtrlTransMax := 2};
  }
  constraint fractions_c {
    if (cfg.seq_cfg.trigger_prog_res_fault) fractions inside {[17:32]};
    else fractions dist { [1:4] := 4, [5:15] := 1, 16 := 1};
    cfg.seq_cfg.addr_flash_word_aligned -> fractions[0] == 1'b0;
  }
  constraint ctrl_info_num_c {
    solve rand_op before ctrl_info_num;
    ctrl_info_num inside {[1 : InfoTypeSize[rand_op.partition >> 1]]};
    if (cfg.ecc_mode > FlashEccEnabled) ctrl_info_num * fractions <= 128;
  }
  constraint ctrl_num_c {
    solve ctrl_data_num, ctrl_info_num, rand_op before ctrl_num;
    if (rand_op.partition == FlashPartData) ctrl_num == ctrl_data_num;
    else ctrl_num == ctrl_info_num;
  }

  constraint rand_op_c {
    solve fractions before rand_op.addr;
    solve flash_program_data before rand_op;
    solve rand_op.partition before rand_op.prog_sel, rand_op.addr;
    solve rand_op.addr before rand_op.otf_addr;
    solve rand_op.addr before rand_op.num_words;

    if (cfg.seq_cfg.op_readonly_on_info_partition) {
      if (cfg.seq_cfg.avoid_ro_partitions) {
        rand_op.partition != FlashPartInfo;
      } else {
        rand_op.partition == FlashPartInfo -> rand_op.op == flash_ctrl_pkg::FlashOpRead;
      }
    }
    if (cfg.seq_cfg.op_readonly_on_info1_partition) {
      if (cfg.seq_cfg.avoid_ro_partitions) {
        rand_op.partition != FlashPartInfo1;
      } else {
        rand_op.partition == FlashPartInfo1 -> rand_op.op == flash_ctrl_pkg::FlashOpRead;
      }
    }

    rand_op.partition dist { FlashPartData := 1, [FlashPartInfo:FlashPartInfo2] :/ 1};
    rand_op.addr[TL_AW-1:BusAddrByteW] == 'h0;
    rand_op.addr[1:0] == 'h0;
    cfg.seq_cfg.addr_flash_word_aligned -> rand_op.addr[2] == 1'b0;
    // If address starts from 0x4 and full prog_win size access(16),
    // transaction creates prog_win error.
    // To prevent that, make full size access always start from address[2:0] == 0.
    if (fractions == 16) rand_op.addr[2] == 0;
    // Make sure that the operation will not cross the selected partition boundries.
    if (rand_op.partition != FlashPartData) {
      rand_op.addr inside
        {[0:InfoTypeBytes[rand_op.partition>>1]-(FlashBankBytesPerWord*fractions)]};
      rand_op.prog_sel == 1;
    } else {
      rand_op.prog_sel == 0;
    }
    if (cfg.ecc_mode > FlashEccEnabled) {
      if (rand_op.partition == FlashPartData) {
        rand_op.addr[18:17] == cfg.tgt_pre[rand_op.partition][cfg.seq_cfg.ecc_err_target];
      } else {
        rand_op.addr[10:9] == cfg.tgt_pre[rand_op.partition][cfg.seq_cfg.ecc_err_target];
      }
    }
    rand_op.otf_addr == rand_op.addr[BusAddrByteW-2:0];
    // Maybe remove this to avoid constraint complexity?
    rand_op.num_words == fractions;
  }
  constraint special_info_acc_c {
    allow_spec_info_acc dist { 3'h7 := 1, 3'h0 := 1, [1:6] :/ 2};
  }

  // If the partition that selected configured as read-only, set otf_wr_pct to 0 to make sure to
  // not program those partitions.
  int otf_wr_pct_temp, otf_bwr_pct_temp;
  function void sync_otf_wr_ro_part();
    if ((cfg.seq_cfg.op_readonly_on_info_partition &&
         rand_op.partition == FlashPartInfo) ||
        (cfg.seq_cfg.op_readonly_on_info1_partition &&
         rand_op.partition == FlashPartInfo1)) begin
      otf_wr_pct_temp = cfg.otf_wr_pct;
      otf_bwr_pct_temp = cfg.otf_bwr_pct;
      cfg.otf_wr_pct = 0;
      cfg.otf_bwr_pct = 0;
    end else begin
      cfg.otf_wr_pct = otf_wr_pct_temp;
      cfg.otf_bwr_pct = otf_bwr_pct_temp;
    end
  endfunction : sync_otf_wr_ro_part

  function void post_randomize();
    super.post_randomize();
    foreach (rand_regions[i]) begin
      if (cfg.en_always_read) rand_regions[i].read_en = MuBi4True;
      if (cfg.en_always_prog) rand_regions[i].program_en = MuBi4True;
      if (cfg.en_always_erase) rand_regions[i].erase_en = MuBi4True;
    end
    foreach (rand_info[i, j, k]) begin
      if (cfg.en_always_read) rand_info[i][j][k].read_en = MuBi4True;
      if (cfg.en_always_prog) rand_info[i][j][k].program_en = MuBi4True;
      if (cfg.en_always_erase) rand_info[i][j][k].erase_en = MuBi4True;
    end
    if (cfg.en_all_info_acc) allow_spec_info_acc = 3'h7;

    // overwrite secret_partition cfg with hw_cfg0
    rand_info[0][0][1] = conv2env_mp_info(flash_ctrl_pkg::CfgAllowRead);
    rand_info[0][0][2] = conv2env_mp_info(flash_ctrl_pkg::CfgAllowRead);
  endfunction : post_randomize

  virtual task pre_start();
    bit csr_test_mode = 0;
    string run_seq_name = "";
    // Erased page doesn't go through descramble.
    // To maintain high stress rate,
    // keep flash_init to FlashMemInitRandomize

    void'($value$plusargs("csr_test_mode=%0b", csr_test_mode));
    void'($value$plusargs("run_%0s", run_seq_name));
    if (csr_test_mode == 1 ||
        run_seq_name inside{"tl_intg_err", "sec_cm_fi"}) begin
      cfg.skip_init = 1;

      super.pre_start();
    end else begin
      flash_init_c.constraint_mode(0);
      if (cfg.ecc_mode > FlashEccEnabled) begin
        foreach (cfg.tgt_pre[partition]) begin
          cfg.tgt_pre[partition].shuffle();
          `uvm_info("cfg_summary",
                    $sformatf("prefix:%s:rd:%2b dr:%2b wr:%2b er:%2b",
                              partition.name, cfg.tgt_pre[partition][TgtRd],
                              cfg.tgt_pre[partition][TgtDr], cfg.tgt_pre[partition][TgtWr],
                              cfg.tgt_pre[partition][TgtEr]),
                    UVM_MEDIUM)
        end
      end
      flash_init = otf_flash_init;

      init_p2r_map();
      `uvm_info("cfg_summary",
                $sformatf({"flash_init:%s ecc_mode %s allow_spec_info_acc:%3b",
                           " scr_ecc_cfg:%s always_read:%0d"},
                          flash_init.name, cfg.ecc_mode.name, allow_spec_info_acc,
                          scr_ecc_cfg.name, cfg.en_always_read),
                UVM_MEDIUM)

      configure_otf_mode();
      super.pre_start();
      if (cfg.seq_cfg.en_init_keys_seeds == 1) begin
        `DV_SPINWAIT(while (otp_key_init_done != 2'b11) cfg.clk_rst_vif.wait_clks(1);,
                     "timeout waiting  otp_key_init_done", 100_000)
      end

      // Need additional flash update after key init is done
      case (cfg.ecc_mode)
        FlashEccDisabled: begin
          // In this mode, write and read are not separated.
          // When write and read happen at the same address,
          // unexpected ecc error can be created.
          flash_otf_region_cfg();
        end
        FlashEccEnabled: begin
          // This mode use tb memory model.
          flash_otf_region_cfg(.scr_mode(scr_ecc_cfg), .ecc_mode(scr_ecc_cfg));
        end
        default: begin
          flash_otf_region_cfg(.scr_mode(scr_ecc_cfg), .ecc_mode(OTFCfgTrue));
          // update_secret_partition program random data to all secret partition.
          // revert change and keep update only for read zone.
          flash_otf_set_secret_part();
          flash_otf_mem_read_zone_init();
        end
      endcase // case (cfg.ecc_mode)
      if (cfg.ecc_mode > FlashSerrTestMode) begin
        cfg.scb_h.do_alert_check = 0;
      end

      cfg.allow_spec_info_acc = allow_spec_info_acc;
      update_partition_access(cfg.allow_spec_info_acc);
      // Polling init wip is done
      csr_spinwait(.ptr(ral.status.init_wip), .exp_data(1'b0));
      cfg.m_fpp_agent_cfg.mon_start = 1;
      `uvm_info("pre_start", "TEST PARAM SUMMARY", UVM_MEDIUM)
      `uvm_info("pre_start", " ** sequence param", UVM_MEDIUM)
      `uvm_info("pre_start", $sformatf({"  otf_num_rw:%0d otf_num_hr:%0d",
                                        " otf_wr_pct:%0d otf_rd_pct:%0d"},
                                       cfg.otf_num_rw,
                                       cfg.otf_num_hr,
                                       cfg.otf_wr_pct,
                                       cfg.otf_rd_pct), UVM_MEDIUM)

      if (cfg.intr_mode == 1) begin
        cfg.rd_lvl = $urandom_range(1,15);
        cfg.wr_lvl = $urandom_range(1,3);
        `uvm_info("pre_start", $sformatf("interrupt testmode. rd_lvl:%0d wr_lvl:%0d",
                                         cfg.rd_lvl, cfg.wr_lvl), UVM_MEDIUM)

        flash_ctrl_fifo_levels_cfg_intr(cfg.rd_lvl, cfg.wr_lvl);
        flash_ctrl_intr_enable(6'h3c);
      end
    end
    otf_wr_pct_temp     = cfg.otf_wr_pct;
    otf_bwr_pct_temp    = cfg.otf_bwr_pct;
  endtask : pre_start

  // On the fly scoreboard mode
  // This will disable reference memory check in the end of the test
  // as well as all intermediate transaction update for memory model.
  function void configure_otf_mode();
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::On;
    cfg.seq_cfg.en_init_keys_seeds = 1;
    cfg.scb_check                               = 0;
    cfg.check_full_scb_mem_model                = 0;
    cfg.scb_otf_en = 1;
    foreach (cfg.m_tl_agent_cfgs[i]) begin
      cfg.m_tl_agent_cfgs[i].a_valid_delay_min = 0;
      cfg.m_tl_agent_cfgs[i].a_valid_delay_max = 0;
      cfg.m_tl_agent_cfgs[i].d_valid_delay_min = 0;
      cfg.m_tl_agent_cfgs[i].d_valid_delay_max = 0;
      cfg.m_tl_agent_cfgs[i].a_ready_delay_min = 0;
      cfg.m_tl_agent_cfgs[i].a_ready_delay_max = 0;
      cfg.m_tl_agent_cfgs[i].d_ready_delay_min = 0;
      cfg.m_tl_agent_cfgs[i].d_ready_delay_max = 0;
    end
  endfunction

  // This is to configure the target prefixes for ecc errors.
  protected function void set_ecc_err_target(flash_tgt_prefix_e target);
    cfg.seq_cfg.ecc_err_target = target;
  endfunction

  protected function void get_bank_and_num(input flash_op_t flash_op, ref int bank, ref int num);
    bank = flash_op.addr[OTFBankId];
    num = ctrl_num;
  endfunction

  // Randomizes until a flash operation satisfies the constraints and its address was not
  // previously written. It issues an error when failing after MaxProgAttempts attempts.
  protected function bit try_create_prog_op(ref flash_op_t ctrl, ref int bank, ref int num);
    int attempts = 0;
    bit prev_addr_flash_word_aligned = cfg.seq_cfg.addr_flash_word_aligned;
    bit prev_avoid_ro_partitions = cfg.seq_cfg.avoid_ro_partitions;
    flash_tgt_prefix_e prev_err_target = cfg.seq_cfg.ecc_err_target;

    // Set the config to avoid half-word writes and readonly partitions.
    cfg.seq_cfg.addr_flash_word_aligned = 1'b1;
    cfg.seq_cfg.avoid_ro_partitions = 1'b1;
    set_ecc_err_target(TgtWr);
    while (attempts < MaxProgAttempts) begin
      otf_addr_t end_addr;
      `DV_CHECK_RANDOMIZE_FATAL(this)
      // This should not happen since cfg.seq_cfg.addr_flash_word_aligned is set,
      // but perhaps the constraint solver is not working as expected.
      if (rand_op.addr[2]) begin
        `uvm_info(`gfn, "Constraint solver failure: rand_op.addr[2] is meant to be 0", UVM_LOW)
        rand_op.addr[2] = 0;
        rand_op.otf_addr[2] = 0;
      end
      if (fractions[0]) begin
        `uvm_info(`gfn, "Constraint solver failure: fractions[0] is meant to be 0", UVM_LOW)
        if (fractions == 1) fractions = 2;
        else fractions[0] = 0;
      end
      ctrl = rand_op;
      `DV_CHECK(!rand_op.otf_addr[2])
      get_bank_and_num(ctrl, bank, num);
      end_addr = ctrl.otf_addr + (num * fractions * 4) - 1;
      `uvm_info(`gfn, $sformatf(
                "Address start=%x end=%x num=%x fractions=%x", ctrl.otf_addr, end_addr, num,
                fractions), UVM_MEDIUM)
      if (!address_range_was_written(to_full_addr(ctrl.otf_addr, bank),
                                     to_full_addr(end_addr, bank))) begin
        cfg.seq_cfg.addr_flash_word_aligned = prev_addr_flash_word_aligned;
        cfg.seq_cfg.avoid_ro_partitions = prev_avoid_ro_partitions;
        set_ecc_err_target(prev_err_target);
        return 1'b1;
      end
      ++attempts;
    end
    `DV_CHECK(0, "Too many unsuccessful attempts to create a prog_op")
    cfg.seq_cfg.addr_flash_word_aligned = prev_addr_flash_word_aligned;
    cfg.seq_cfg.avoid_ro_partitions = prev_avoid_ro_partitions;
    set_ecc_err_target(prev_err_target);
    return 1'b0;
  endfunction : try_create_prog_op

  // This detects if two addresses are in different program resolution window.
  protected function bit in_different_prog_win(input otf_addr_t a, input otf_addr_t b);
     return (a >> (FlashPgmResWidth + BusByteWidth)) != (b >> (FlashPgmResWidth + BusByteWidth));
  endfunction

  // This is a helper function for prog_flash. It performs a write operation, places the data
  // in the fifo, checks protection, and checks for program window resolution errors. If the
  // write will proceed it creates an item with the expected results for the scoreboard.
  local task issue_prog_request(input flash_op_t flash_op, ref shortint lcnt, input bit in_err,
                                input bit store_prog_data);
    flash_mp_region_cfg_t region;
    bit expect_prog_win_error = 1'b0;
    bit drop = 1'b0;
    int bank = flash_op.addr[TL_AW-1:OTFBankId];
    otf_addr_t end_addr;

    `uvm_info("prog_flash", $sformatf(
              "addr:%x, otf_addr:%x wd:%0d, ", flash_op.addr, flash_op.otf_addr,
              flash_op.num_words), UVM_MEDIUM)
    flash_program_data = '{};
    // Each flash_program_data[] entry : 4B
    // {global_cnt(16bits), lcnt(16bits)}
    for (int j = 0; j < flash_op.num_words; j++) begin
      if (cfg.wr_rnd_data) begin
        flash_program_data.push_back($urandom);
      end else begin
        flash_program_data.push_back({global_pat_cnt, lcnt++});
      end
    end
    // Check permissions.
    if (flash_op.partition == FlashPartData) begin
      int page = cfg.addr2page(flash_op.addr);
      region = cfg.get_region(page);
    end else begin
      // for region, use per bank page number
      int page = cfg.addr2page(flash_op.otf_addr);
      region = cfg.get_region_from_info(cfg.mp_info[bank][flash_op.partition>>1][page]);
      drop |= check_info_part(flash_op, "prog_flash");
    end
    drop |= validate_flash_op(flash_op, region);
    if (drop) begin
      `uvm_info("prog_flash", $sformatf("op:%s is not allowed in this region %p",
                                        flash_op.op.name, region), UVM_MEDIUM)
    end

    // Check program window resolution error.
    end_addr = flash_op.otf_addr + flash_op.num_words * 4 - 1;
    if (in_different_prog_win(flash_op.otf_addr, end_addr)) begin
      `uvm_info("prog_flash", $sformatf("prog_window violation, start_addr:0x%x end_addr:0x%x",
                                        flash_op.otf_addr, end_addr), UVM_MEDIUM)
      expect_prog_win_error = 1;
      drop = 1;
    end
    if (drop) set_otf_exp_alert("recov_err");

    // Start the operation.
    if (cfg.intr_mode) begin
      flash_ctrl_intr_write(flash_op, flash_program_data);
    end else begin
      flash_ctrl_start_op(flash_op);
      if (in_err) begin
        cfg.tlul_core_exp_cnt += flash_op.num_words;
      end
      flash_ctrl_write(flash_program_data, !in_err);

      if (!in_err) wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
    end

    if (expect_prog_win_error) begin
      csr_rd_check(.ptr(ral.err_code.prog_win_err), .compare_value(1));
      drop = 1;
    end

    `uvm_info("prog_flash", $sformatf("bank:%0d addr:%x otf_addr:%x part:%s wd:%0d",
                                      bank, flash_op.addr, flash_op.otf_addr,
                                      flash_op.partition.name, flash_op.num_words), UVM_MEDIUM)
    if (drop) begin
      uvm_reg_data_t ldata;
      csr_rd(.ptr(ral.err_code), .value(ldata), .backdoor(1));
      `uvm_info("prog_flash", $sformatf("skip sb path due to err_code:%x", ldata), UVM_MEDIUM)
    end else begin
      flash_otf_item exp_item;
      if (store_prog_data) cfg.prog_data[flash_op] = flash_program_data;

      flash_otf_print_data64(flash_program_data, "wdata");
      `uvm_create_obj(flash_otf_item, exp_item)

      exp_item.cmd = flash_op;
      exp_item.dq = flash_program_data;
      exp_item.region = region;
      // Scramble data
      exp_item.scramble(otp_addr_key, otp_data_key, flash_op.otf_addr);

      p_sequencer.eg_exp_ctrl_port[bank].write(exp_item);
      flash_phy_prim_agent_pkg::print_flash_data(exp_item.fq,
          $sformatf("fdata_%0d bank %0d", cfg.otf_ctrl_wr_sent, bank));
    end
    global_pat_cnt++;
    cfg.otf_ctrl_wr_sent++;
  endtask

  // Program flash in the unit of minimum resolution (4Byte)
  // If data is not aligned to 8Byte, rtl pads all F to
  // upper or lower 4Byte.
  // @arg: flash_op_p : command struct return updated address after write
  // @arg: bank: bank index to access flash
  // @arg: num : number of 8 words range: [1 : 32]
  // @arg: wd  : number of 4byte (TL bus unit) : default : 16
  // @arg: in_err : inject fatal error causes flash access disable
  virtual task prog_flash(ref flash_op_t flash_op, input int bank, int num, int wd = 16,
                  bit in_err = 0, bit store_prog_data = 0);
    data_q_t flash_data_chunk;
    bit poll_fifo_status = ~in_err;
    shortint lcnt = 0;
    otf_addr_t start_addr, end_addr;
    data_4s_t tmp_data;
    int tot_wd;
    bit overflow = 0;

    `DV_CHECK_EQ(flash_op.otf_addr[2], 1'b0,
                 "prog_flash gets unexpected address not 8 byte aligned")
    `DV_CHECK(wd % 2 == 0, "prog_flash gets unexpected odd bus word count")
    tot_wd = wd * num;

    flash_op.op = FlashOpProgram;
    flash_op.num_words = wd;
    start_addr = flash_op.otf_addr;
    // last byte address in each program
    end_addr = start_addr + (tot_wd * 4) - 1;
    update_range_addresses_written(to_full_addr(start_addr, bank), to_full_addr(end_addr, bank));

    `uvm_info("prog_flash",$sformatf("begin addr:%x part:%s num:%0d wd:%0d st:%x ed:%x",
                                     flash_op.otf_addr, flash_op.partition.name, num,
                                     wd, start_addr, end_addr), UVM_MEDIUM)
/*
    if (cfg.ecc_mode > FlashEccEnabled) begin
      if (flash_op.partition == FlashPartData) begin
        overflow = (end_addr[18:17] != start_addr[18:17] ||
                    end_addr[16:0] > 17'h1_FE00);
      end else begin
        overflow = (end_addr[10:9] != start_addr[10:9]);
      end
    end else begin
      overflow = (start_addr[OTFHostId] != end_addr[OTFHostId]);
    end

    if (overflow) begin
      otf_addr_t tmp_addr = start_addr;
      if (flash_op.partition == FlashPartData) begin
        start_addr[16:0] = 'h0;
      end else begin
        start_addr[8:0] = 'h0;
      end
      `uvm_info("prog_flash", $sformatf({"overflow!, start:%x end:%x part:%s",
                                         " roll over start address to 0x%x"},
                                        tmp_addr, end_addr, flash_op.partition.name,
                                        start_addr), UVM_MEDIUM)
      tot_wd = wd * num;
      end_addr = start_addr + (tot_wd * 4) - 1;
    end
  */
    // Roll over start address if this is the case.
    `uvm_info("prog_flash", $sformatf({"bank:%0d otf_addr:0x%0h,",
                                       " part:%s size:%0d x %0d x 4B"},
                                      bank, flash_op.otf_addr, flash_op.partition.name,
                                      num, wd), UVM_MEDIUM)

    flash_op.otf_addr = start_addr;

    for (int i = 0; i < num; i++) begin : num_loop
      end_addr = flash_op.otf_addr + (wd * 4) - 1;

      flash_op.addr = flash_op.otf_addr;
      flash_op.addr[TL_AW-1:OTFBankId] = bank;

      `DV_CHECK_EQ(flash_op.addr[2], 1'b0, "Unexpected address not 8-byte aligned for flash_prog")
      `uvm_info("prog_flash", $sformatf("in loop tl_addr:%x start_addr:%x  end_addr:%x",
                                        flash_op.addr, flash_op.otf_addr, end_addr), UVM_MEDIUM)

      // Check resolution error
      // Current resolution : 0x40.
      // If address[6] differ between start and end addr a prog_win error will be raised and the
      // transaction will be dropped. But if cfg.seq_cfg.avoid_prog_res_fault is set this breaks
      // off a transaction up to the window's end, issues it, and adjusts the transactions to
      // come to start past the window's end.
      if (in_different_prog_win(flash_op.otf_addr, end_addr) &&
          cfg.seq_cfg.avoid_prog_res_fault) begin
        flash_op_t tmp_op = flash_op;
        flash_op_t split_op;
        int split_wd;
        otf_addr_t next_addr;
        do begin
          // The next address needs to be at the next window resolution start.
          next_addr = round_to_prog_resolution(
               tmp_op.otf_addr + flash_ctrl_reg_pkg::RegBusPgmResBytes);
          `DV_CHECK_NE(next_addr - 1, end_addr, "Should not break up to end_addr")
          split_wd = (next_addr - tmp_op.otf_addr) >> 2;
          split_op = tmp_op;
          split_op.num_words = split_wd;
          `uvm_info("prog_flash", $sformatf(
                    "Broke request below into one up to 0x%x with %0d bus words",
                    next_addr, split_wd), UVM_MEDIUM)
          print_flash_op(tmp_op, UVM_MEDIUM);
          `uvm_info("prog_flash", "Broken request first", UVM_MEDIUM)
          print_flash_op(split_op, UVM_MEDIUM);
          tmp_op.addr = {bank, next_addr};
          tmp_op.otf_addr = tmp_op.addr;
          tmp_op.num_words -= split_wd;
          `uvm_info("prog_flash", "Broken request second", UVM_MEDIUM)
          print_flash_op(tmp_op, UVM_MEDIUM);
          issue_prog_request(split_op, lcnt, in_err, store_prog_data);
        end while (in_different_prog_win(tmp_op.otf_addr, end_addr));
        issue_prog_request(tmp_op, lcnt, in_err, store_prog_data);
      end else begin
        issue_prog_request(flash_op, lcnt, in_err, store_prog_data);
      end
      flash_op.otf_addr += wd * 4;
    end : num_loop
  endtask : prog_flash

  // Read flash in the unit of minimum resolution (4 Byte).
  // 1 word : 8Byte
  // @arg: flash_op_p : command struct return updated address after write
  // @arg: bank: bank index to access flash
  // @arg: num : number of 8 words range: [1 : 32]
  // @arg: wd  : number of 4byte (TL bus unit) : default : 16
  // @arg: overrd : invoke oversize read
  // @arg: in_err : inject fatal error causes flash access disable
  virtual task read_flash(ref flash_op_t flash_op, input int bank, int num, int wd = 16,
                  int overrd = 0, bit in_err = 0);
    data_q_t flash_read_data;
    flash_otf_item exp_item;
    bit poll_fifo_status = ~in_err;
    bit [flash_ctrl_pkg::BusAddrByteW-1:0] start_addr, end_addr;
    int page;
    bit overflow = 0;
    uvm_reg_data_t reg_data;
    bit derr_is_set;
    bit drop;
    int size, is_odd, tail;
    addr_t tmp_addr;
    flash_mp_region_cfg_t my_region;
    rd_cache_t rd_entry;

    // Exclude secret partition from non scrambled / ecc mode
    if (cfg.ecc_mode == FlashEccDisabled &&
        flash_op.partition == FlashPartInfo) return;

    flash_op.op = FlashOpRead;
    flash_op.num_words = wd;
    start_addr = flash_op.otf_addr;
    end_addr = start_addr + (wd * 4 * num) - 1;

    if (cfg.ecc_mode > FlashEccEnabled) begin
      if (flash_op.partition == FlashPartData) begin
        overflow = (end_addr[18:17] != start_addr[18:17] ||
                    end_addr[16:0] > 17'h1_FE00);
      end else begin
        overflow = (end_addr[10:9] != start_addr[10:9]);
      end
    end else begin
      // Ctrl read takes lower half of each bank
      // and host read takes upper half.
      overflow = end_addr[OTFHostId];
    end

    if (overflow) begin
      if (flash_op.partition == FlashPartData) begin
        flash_op.otf_addr[16:0] = 'h0;
      end else begin
        flash_op.otf_addr[8:0] = 'h0;
      end
      `uvm_info("read_flash", $sformatf("overflow!, roll over start address to 0x%x",
                                flash_op.otf_addr), UVM_MEDIUM)
    end

    for (int i = 0; i < num; i++) begin
      drop = 0;
      flash_op.addr = flash_op.otf_addr;
      flash_op.addr[TL_AW-1:OTFBankId] = bank;
      rd_entry.bank = bank;
      is_odd = flash_op.addr[2];
      size = (flash_op.num_words + is_odd) / 2;
      tail = (flash_op.num_words + is_odd) % 2;
      tmp_addr = flash_op.addr;
      flash_op.addr[2:0] = 0;

      // Per Qword loop
      `uvm_create_obj(flash_otf_item, exp_item)
      for (int i = 0; i < size; i++) begin
        if (flash_op.partition == FlashPartData) begin
          page = cfg.addr2page(flash_op.addr);
          my_region = cfg.get_region(page);
        end else begin
          page = cfg.addr2page(flash_op.otf_addr);
          my_region = cfg.get_region_from_info(cfg.mp_info[bank][flash_op.partition>>1][page]);
          `uvm_info(`gfn, $sformatf(
                    "For addr:%x, bank:%0d, page:%0d, region scr_en:%b ecc_en:%b",
                    flash_op.otf_addr, bank, page, my_region.scramble_en == MuBi4True,
                    my_region.ecc_en == MuBi4True), UVM_MEDIUM)
          drop |= check_info_part(flash_op, "read_flash");
        end
        drop |= validate_flash_op(flash_op, my_region);
        flash_op.addr += 8;
        flash_op.otf_addr += 8;
        exp_item.ctrl_rd_region_q.push_back(my_region);
      end // for (int i = 0; i < size; i++)
      if (tail) begin
        if (flash_op.partition == FlashPartData) begin
          page = cfg.addr2page(flash_op.addr);
          my_region = cfg.get_region(page);
        end else begin
          page = cfg.addr2page(flash_op.otf_addr);
          my_region = cfg.get_region_from_info(cfg.mp_info[bank][flash_op.partition>>1][page]);
          drop |= check_info_part(flash_op, "read_flash");
        end
        drop |= validate_flash_op(flash_op, my_region);
        exp_item.ctrl_rd_region_q.push_back(my_region);
      end
      flash_op.addr = tmp_addr;
      // Bank id truncated by otf_addr size
      flash_op.otf_addr = tmp_addr;
      // recalculate page and region based on start address
      // for the debug print
      if  (flash_op.partition == FlashPartData) begin
        page = cfg.addr2page(flash_op.addr);
        my_region = cfg.get_region(page);
      end else begin
        page = cfg.addr2page(flash_op.otf_addr);
        my_region = cfg.get_region_from_info(cfg.mp_info[bank][flash_op.partition>>1][page]);
      end
      if (drop) begin
        `uvm_info("read_flash", $sformatf("op:%s is not allowed in the region:%p",
                                          flash_op.op.name, my_region), UVM_MEDIUM)
        set_otf_exp_alert("recov_err");
      end
      `uvm_info("read_flash",
                $sformatf({"bank:%0d page:%0d otf_addr:0x%0h,",
                           " part:%s size:%0d x %0d x 4B start_addr:%x  end_addr:%x",
                           " overrd:%0d"},
                          bank, page, flash_op.otf_addr,
                          flash_op.partition.name, num, wd, start_addr, end_addr, overrd),
                UVM_MEDIUM)
      exp_item.cmd = flash_op;
      // per bank address is used for decryption in sbx
      exp_item.start_addr = flash_op.otf_addr;
      exp_item.addr_key = otp_addr_key;
      exp_item.data_key = otp_data_key;

      rd_entry.addr = flash_op.otf_addr;
      // Address has to be 8byte aligned
      rd_entry.addr[2:0] = 'h0;
      rd_entry.part = flash_op.partition;
      if (cfg.ecc_mode > FlashEccEnabled) begin
        if (drop == 0) begin
          if (cfg.ecc_mode == FlashSerrTestMode || flash_op.addr[2] == 0) begin
            cfg.add_bit_err(flash_op, ReadTaskCtrl, exp_item);
          end
        end
      end

      cfg.otf_read_entry.insert(rd_entry, flash_op);
      if (cfg.derr_once) begin
        derr_is_set = cfg.derr_created[ReadTaskCtrl] & ~global_derr_is_set;
      end else begin
        derr_is_set = cfg.derr_created[ReadTaskCtrl];
      end
      if (derr_is_set) begin
        `uvm_info("read_flash", $sformatf("assert_derr 0x%x",
                                          {flash_op.addr[31:3], 3'h0}), UVM_MEDIUM)
        global_derr_is_set = 1;
        if (cfg.scb_h.do_alert_check == 1) begin
          cfg.scb_h.expected_alert["fatal_err"].expected = 1;
          cfg.scb_h.expected_alert["fatal_err"].max_delay = 2000;
          cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

          cfg.scb_h.expected_alert["recov_err"].expected = 1;
          cfg.scb_h.expected_alert["recov_err"].max_delay = 2000;
          cfg.scb_h.exp_alert_contd["recov_err"] = 10000;
        end
      end

      `uvm_info("read_flash", $sformatf("intr_mode=%b", cfg.intr_mode), UVM_MEDIUM)
      if (cfg.intr_mode) begin
        flash_ctrl_intr_read(flash_op, flash_read_data);
      end else begin
        flash_ctrl_start_op(flash_op);
        if (in_err) begin
           cfg.tlul_core_exp_cnt += flash_op.num_words;
        end
        flash_ctrl_read(flash_op.num_words, flash_read_data, poll_fifo_status);

        if (overrd > 0) begin
          overread(flash_op, bank, num, overrd);
        end
        if (!in_err) wait_flash_op_done();
      end

      if (derr_is_set | cfg.ierr_created[ReadTaskCtrl]) begin
        `uvm_info("read_flash", $sformatf(
                  "bank:%0d addr: %x(otf:%x) derr_is_set:%0d ierr_created[ReadTaskCtrl]:%0d",
                  bank, flash_op.addr, flash_op.otf_addr, derr_is_set,
                  cfg.ierr_created[ReadTaskCtrl]),
                  UVM_MEDIUM)
        csr_rd_check(.ptr(ral.op_status.err), .compare_value(1));
        csr_rd_check(.ptr(ral.err_code.rd_err), .compare_value(1));
        reg_data = get_csr_val_with_updated_field(ral.err_code.rd_err, reg_data, 1);
        csr_wr(.ptr(ral.err_code), .value(reg_data));
        reg_data = get_csr_val_with_updated_field(ral.op_status.err, reg_data, 0);
        csr_wr(.ptr(ral.op_status), .value(reg_data));
        if (cfg.derr_once == 0) cfg.derr_created[ReadTaskCtrl] = 0;
        cfg.ierr_created[ReadTaskCtrl] = 0;
      end

      exp_item.exp_err |= in_err;
      exp_item.dq = flash_read_data;
      exp_item.fq = exp_item.dq2fq(flash_read_data);

      if (drop) begin
        `uvm_info("read_flash", "skip sb path due to err", UVM_MEDIUM)
      end else begin
        p_sequencer.eg_exp_ctrl_port[bank].write(exp_item);
      end
      cfg.otf_ctrl_rd_rcvd++;
      flash_op.otf_addr = flash_op.otf_addr + (4 * wd);
    end // for (int i = 0; i < num; i++)
  endtask // read_flash

  // Read error behavior task
  // This task issue rd_fifo read without setting stat_op.
  // Expected output is to received errored response from core_tl interface.
  task overread(flash_op_t flash_op, int bank, int num, int wd);
    data_q_t flash_read_data;
    bit poll_fifo_status = 0;
    addr_t addr = ral.rd_fifo.get_address();

    repeat (wd) cfg.scb_h.over_rd_err[addr]++;
    cfg.m_tl_agent_cfg.check_tl_errs = 0;
    `uvm_info("overread", $sformatf("addr is set 0x%x wd:%0d", addr, wd),
              UVM_MEDIUM)
    flash_ctrl_read(wd, flash_read_data, poll_fifo_status, 1);
    cfg.m_tl_agent_cfg.check_tl_errs = 1;
  endtask // overread

  // Direct access from the host. It returns multiple of
  // 4bytes of data.
  // @arg : addr : Direct access address.
  //               At the phy interface, address_phy = addr >> 3,
  //               because phy returns data in 8byte.
  //               At the host interface, addr[2] is used for
  //               word selector s.t.
  //               addr[2]? upper 4byte : lower 4byte of phy data.
  // @arg : bank : bank index to access flash.
  // @arg : num  : number of 4byte data to read countinuously
  //               by 4 byte apart.
  // @arg: in_err : inject fatal error causes flash access disable
  virtual task otf_direct_read(bit [OTFHostId-2:0] addr, int bank, int num, bit in_err);
    bit[TL_AW-1:0] tl_addr, st_addr, end_addr;
    data_4s_t rdata;
    flash_otf_item exp_item;
    int page;
    flash_op_t flash_op;
    bit completed;
    bit derr_is_set;
    bit derr, drop;
    bit overflow = 0;
    flash_mp_region_cfg_t my_region;
    rd_cache_t rd_entry;

    if (cfg.ecc_mode > FlashEccEnabled) begin
      end_addr = addr + num * 4 - 1;
      overflow = (end_addr[OTFHostId:0] > 18'h1_FE00);
      tl_addr[OTFHostId-:2] = cfg.tgt_pre[FlashPartData][TgtDr];
    end else begin
      end_addr = addr + num * 4 - 1;
      tl_addr[OTFHostId] = 1;
      overflow = end_addr[OTFHostId];
    end
    `uvm_info("direct_read", $sformatf("addr: %x end_addr: %x overflow: %x",
                                       addr, end_addr, overflow), UVM_HIGH)
    rd_entry.bank = bank;
    tl_addr[TL_AW-1:OTFBankId] = bank;
    if (overflow) begin
       addr = num * 4;
    end
    tl_addr[OTFHostId-2:2] = addr[OTFHostId-2:2];

    `uvm_info("direct_read", $sformatf("bank:%0d tl_addr:0x%0h, num: %0d",
                                       bank, tl_addr, num), UVM_MEDIUM)
    // Capture for the print in sb.
    st_addr = tl_addr;
    for (int i = 0; i < num ; i++) begin
      drop = 0;
      derr = 0;
      // force address wrap around
      if (cfg.ecc_mode > FlashEccEnabled) tl_addr[18:17] = cfg.tgt_pre[FlashPartData][TgtDr];

      `uvm_create_obj(flash_otf_item, exp_item)
      page = cfg.addr2page(tl_addr[OTFBankId:0]);
      my_region = cfg.get_region(page);
      flash_op.op = FlashOpRead;

      exp_item.page = page;
      exp_item.region = my_region;
      exp_item.start_addr = tl_addr;
      exp_item.addr_key = otp_addr_key;
      exp_item.data_key = otp_data_key;

      // Address should be per bank addr
      rd_entry.addr = tl_addr;
      rd_entry.addr[TL_AW-1:OTFBankId] = 0;

      // Address has to be 8byte aligned
      rd_entry.addr[2:0] = 'h0;
      rd_entry.part = FlashPartData;

      if (cfg.ecc_mode > FlashEccEnabled) begin
        if (exp_item.region.ecc_en == MuBi4True) begin
          flash_op.addr = tl_addr;
          // host can only access data partitions.
          flash_op.partition = FlashPartData;
          flash_op.num_words = 1;
          if (cfg.ecc_mode == FlashSerrTestMode || tl_addr[2] == 0) begin
            cfg.add_bit_err(flash_op, ReadTaskHost, exp_item);
          end
          if (cfg.derr_once) begin
            derr_is_set = cfg.derr_created[ReadTaskHost] & ~global_derr_is_set;
          end else begin
            derr_is_set = (cfg.derr_created[ReadTaskHost] | cfg.ierr_created[ReadTaskHost]);
          end

          if (derr_is_set) begin
            `uvm_info("direct_read", $sformatf("assert_derr 0x%x", tl_addr), UVM_MEDIUM)
            cfg.scb_h.ecc_error_addr[{tl_addr[31:3],3'h0}] = 1;
            global_derr_is_set = 1;
          end
          if (cfg.derr_once == 0) cfg.derr_created[ReadTaskHost] = 0;
          `uvm_info("direct_read", $sformatf(
                    "ierr_created[ReadTaskHost]:%0d  derr_is_set:%0d exists:%0d",
                    cfg.ierr_created[ReadTaskHost], derr_is_set,
                    cfg.scb_h.ecc_error_addr.exists({tl_addr[31:3],3'h0})),
                    UVM_MEDIUM)
          cfg.ierr_created[ReadTaskHost] = 0;
        end
        if (cfg.scb_h.ecc_error_addr.exists({tl_addr[31:3],3'h0}) | derr_is_set) derr = 1;
      end
      cfg.otf_read_entry.insert(rd_entry, flash_op);
      `uvm_info("direct_read", $sformatf({"num_i:%0d bank:%0d exec: page:%0d(%0d)",
                                          " 0x%x derr:%0d in_err:%0d"},
                                         i, bank, tl_addr, page, (page % 256),
                                         derr, in_err), UVM_MEDIUM)
      if (in_err) cfg.scb_h.in_error_addr[{tl_addr[31:3],3'h0}] = 1;

      derr |= in_err;

      if (cfg.ecc_mode > FlashSerrTestMode) begin
        if (derr & cfg.scb_h.do_alert_check) begin
          cfg.scb_h.expected_alert["fatal_err"].expected = 1;
          cfg.scb_h.expected_alert["fatal_err"].max_delay = cfg.seq_cfg.long_fatal_err_delay;
          cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;
        end
      end

      // in_err is currently used to address error caused by disable flash.
      if (in_err) begin
         set_otf_exp_alert("fatal_err");
      end

      cfg.inc_otd_tbl(bank, tl_addr, FlashPartData);
      d_cnt1++;
      do_direct_read(.addr(tl_addr), .mask('1), .blocking(1), .rdata(rdata),
                     .completed(completed), .exp_err_rsp(derr));
      d_cnt2++;
      `uvm_info(`gfn, $sformatf("direct_read_trace: sent:%0d rcvd:%0d", d_cnt1, d_cnt2),
                UVM_HIGH)
      // issue csr rd to capture coverpoint at sb.
      if (derr) begin
        uvm_reg_data_t ldata;
        csr_rd(.ptr(ral.err_code), .value(ldata));
      end
      if (completed) begin
        exp_item.dq.push_back(rdata);
        exp_item.exp_err |= in_err;

        p_sequencer.eg_exp_host_port[bank].write(exp_item);
        `uvm_info("direct_read",
                  $sformatf("SEQ:st_addr:%x addr:%x rcvd:%0d rdata:%x derr:%0d",
                            st_addr, tl_addr, cfg.otf_host_rd_rcvd, rdata, derr),
                  UVM_MEDIUM)
      end else begin
        `uvm_info("direct_read",
                  $sformatf("SEQ:st_addr:%x addr:%x rcvd:%0d aborted  derr:%0d",
                            st_addr, tl_addr, cfg.otf_host_rd_rcvd, derr),
                  UVM_MEDIUM)
      end
      cfg.dec_otd_tbl(bank, tl_addr, FlashPartData);
      cfg.otf_host_rd_rcvd++;
      tl_addr += 4;
    end
  endtask // otf_direct_read

  // Read flash in the unit of minimum resolution (4 Byte).
  // This task has following difference from 'task read_flash'
  //   - This task doesn't use target prefix (tgt_pre).
  //   - If same address write happens, the address marked as error and
  //     set expected alert
  //   - num and wd is controlled by test sequence to keep read within
  //     'loaded zone'
  //
  // @arg: flash_op_p : command struct return updated address after write
  // @arg: bank: bank index to access flash
  // @arg: num : number of 8 words range: [1 : 32]
  // @arg: wd  : number of 4byte (TL bus unit) : default : 16
  task readback_flash(flash_op_t flash_op, int bank, int num, int wd = 16);
    data_q_t flash_read_data;
    flash_otf_item exp_item;
    bit poll_fifo_status = 1;
    int page;

    uvm_reg_data_t reg_data;
    bit derr_is_set;
    bit drop;
    int size, is_odd, tail;
    addr_t tmp_addr;
    flash_mp_region_cfg_t my_region;
    rd_cache_t rd_entry;

    flash_op.op = FlashOpRead;
    flash_op.num_words = wd;

    for (int i = 0; i < num; i++) begin
      drop = 0;
      flash_op.addr = flash_op.otf_addr;
      flash_op.addr[TL_AW-1:OTFBankId] = bank;
      rd_entry.bank = bank;
      is_odd = flash_op.addr[2];
      size = (flash_op.num_words + is_odd) / 2;
      tail = (flash_op.num_words + is_odd) % 2;
      tmp_addr = flash_op.addr;
      flash_op.addr[2:0] = 0;

      // Per Qword loop
      `uvm_create_obj(flash_otf_item, exp_item)
      exp_item.addr_key = otp_addr_key;
      exp_item.data_key = otp_data_key;

      for (int i = 0; i < size; i++) begin
        if (flash_op.partition == FlashPartData) begin
          page = cfg.addr2page(flash_op.addr);
          my_region = cfg.get_region(page);
        end else begin
          page = cfg.addr2page(flash_op.otf_addr);
          my_region = cfg.get_region_from_info(cfg.mp_info[bank][flash_op.partition>>1][page]);
          drop |= check_info_part(flash_op, "readback_flash");
        end
        drop |= validate_flash_op(flash_op, my_region);
        exp_item.ctrl_rd_region_q.push_back(my_region);

         rd_entry.addr = flash_op.otf_addr;
         // Address has to be 8byte aligned
         rd_entry.addr[2:0] = 'h0;
         rd_entry.part = flash_op.partition;
//`JDBG(("readback_flash: rd_entry:%p  exist:%0d", rd_entry, cfg.otf_scb_h.corrupt_entry.exists(rd_entry)))
         if (drop == 0 &&
             my_region.ecc_en == MuBi4True &&
             cfg.otf_scb_h.corrupt_entry.exists(rd_entry) == 1) begin
            `uvm_info("readback_flash", $sformatf("read corrupted entry 0x%x",
                                                  {flash_op.addr[31:3], 3'h0}), UVM_MEDIUM)
            derr_is_set |= 1;
         end

        flash_op.addr += 8;
        flash_op.otf_addr += 8;
      end // for (int i = 0; i < size; i++)
      if (tail) begin
        if (flash_op.partition == FlashPartData) begin
          page = cfg.addr2page(flash_op.addr);
          my_region = cfg.get_region(page);
        end else begin
          page = cfg.addr2page(flash_op.otf_addr);
          my_region = cfg.get_region_from_info(cfg.mp_info[bank][flash_op.partition>>1][page]);
          drop |= check_info_part(flash_op, "readback_flash");
        end
        drop |= validate_flash_op(flash_op, my_region);
        exp_item.ctrl_rd_region_q.push_back(my_region);

        rd_entry.addr = flash_op.otf_addr;
        // Address has to be 8byte aligned
        rd_entry.addr[2:0] = 'h0;
        rd_entry.part = flash_op.partition;
        if (drop == 0 &&
            my_region.ecc_en == MuBi4True &&
            cfg.otf_scb_h.corrupt_entry.exists(rd_entry) == 1) begin
          `uvm_info("readback_flash", $sformatf("read corrupted entry 0x%x",
                                                {flash_op.addr[31:3], 3'h0}), UVM_MEDIUM)
          derr_is_set |= 1;
        end
      end
      flash_op.addr = tmp_addr;
      // Bank id truncaded by otf_addr size
      flash_op.otf_addr = tmp_addr;

      // recalculate page and region based on start address
      // for the debug print
      if  (flash_op.partition == FlashPartData) begin
        page = cfg.addr2page(flash_op.addr);
        my_region = cfg.get_region(page);
      end else begin
        page = cfg.addr2page(flash_op.otf_addr);
        my_region = cfg.get_region_from_info(cfg.mp_info[bank][flash_op.partition>>1][page]);
      end
      if (drop) begin
        `uvm_info("readback_flash", $sformatf("op:%s is not allowed in the region:%p",
                                          flash_op.op.name, my_region), UVM_MEDIUM)
        set_otf_exp_alert("recov_err");
      end
      `uvm_info("readback_flash",
                $sformatf({"bank:%0d page:%0d otf_addr:0x%0h,",
                           " part:%s size:%0d x %0d x 4B"},
                          bank, page, flash_op.otf_addr,
                          flash_op.partition.name, num, wd),
                UVM_MEDIUM)

      exp_item.cmd = flash_op;
      // per bank address is used for decryption in sbx
      exp_item.start_addr = flash_op.otf_addr;

      rd_entry.addr = flash_op.otf_addr;
      // Address has to be 8byte aligned
      rd_entry.addr[2:0] = 'h0;
      rd_entry.part = flash_op.partition;

      if (cfg.ecc_mode > FlashEccEnabled) begin
        if (exp_item.region.ecc_en == MuBi4True && drop == 0) begin
          if (cfg.ecc_mode == FlashSerrTestMode || flash_op.addr[2] == 0) begin
            cfg.add_bit_err(flash_op, ReadTaskCtrl, exp_item);
          end
        end
      end

      cfg.otf_read_entry.insert(rd_entry, flash_op);

      if (derr_is_set) begin
        `uvm_info("readback_flash", $sformatf("read corrupted entry 0x%x",
                                          {flash_op.addr[31:3], 3'h0}), UVM_MEDIUM)
        global_derr_is_set = 1;
        derr_is_set = 1;
        exp_item.derr = 1;

        if (cfg.scb_h.do_alert_check == 1) begin
          cfg.scb_h.expected_alert["fatal_err"].expected = 1;
          cfg.scb_h.expected_alert["fatal_err"].max_delay = 2000;
          cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

          cfg.scb_h.expected_alert["recov_err"].expected = 1;
          cfg.scb_h.expected_alert["recov_err"].max_delay = 2000;
          cfg.scb_h.exp_alert_contd["recov_err"] = 10000;
        end
      end
      if (cfg.intr_mode) begin
        flash_ctrl_intr_read(flash_op, flash_read_data);
      end else begin
        flash_ctrl_start_op(flash_op);
        flash_ctrl_read(flash_op.num_words, flash_read_data, poll_fifo_status);
        wait_flash_op_done();
      end

      if (derr_is_set | cfg.ierr_created[ReadTaskCtrl]) begin
        uvm_reg_data_t ldata;
        csr_rd(.ptr(ral.err_code), .value(ldata), .backdoor(1));
        `uvm_info("readback_flash", $sformatf(
                  "bank:%0d addr: %x(otf:%x) derr_is_set:%0d ierr_created[ReadTaskCtrl]:%0d",
                  bank, flash_op.addr, flash_op.otf_addr, derr_is_set,
                  cfg.ierr_created[ReadTaskCtrl]),
                  UVM_MEDIUM)
        csr_rd_check(.ptr(ral.op_status.err), .compare_value(1));
        csr_rd_check(.ptr(ral.err_code.rd_err), .compare_value(1));
        reg_data = get_csr_val_with_updated_field(ral.err_code.rd_err, reg_data, 1);
        csr_wr(.ptr(ral.err_code), .value(reg_data));
        reg_data = get_csr_val_with_updated_field(ral.op_status.err, reg_data, 0);
        csr_wr(.ptr(ral.op_status), .value(reg_data));
        if (cfg.derr_once == 0) cfg.derr_created[ReadTaskCtrl] = 0;
        cfg.ierr_created[ReadTaskCtrl] = 0;
      end

      exp_item.dq = flash_read_data;
      exp_item.fq = exp_item.dq2fq(flash_read_data);
      if (drop) begin
        `uvm_info("read_flash", "skip sb path due to err", UVM_MEDIUM)
         csr_wr(.ptr(ral.op_status), .value(0));

      end else begin
        p_sequencer.eg_exp_ctrl_port[bank].write(exp_item);
      end
      cfg.otf_ctrl_rd_rcvd++;
      flash_op.otf_addr = flash_op.otf_addr + (4 * wd);
    end // for (int i = 0; i < num; i++)
  endtask

   task direct_readback(bit [OTFBankId-1:0] addr, int bank, int num);
     bit[TL_AW-1:0] tl_addr, st_addr, end_addr;
    data_4s_t rdata;
    flash_otf_item exp_item;
    int page;
    flash_op_t flash_op;
    bit completed;
    bit derr_is_set;
    bit derr, drop;
    bit overflow = 0;
    flash_mp_region_cfg_t my_region;
    rd_cache_t rd_entry;

    rd_entry.bank = bank;
    tl_addr[TL_AW-1:OTFBankId] = bank;
    tl_addr[OTFHostId:2] = addr[OTFHostId:2];

    `uvm_info("direct_readback", $sformatf("bank:%0d tl_addr:0x%0h, num: %0d",
                                       bank, tl_addr, num), UVM_MEDIUM)
    // Capture for the print in sb.
    st_addr = tl_addr;

     for (int i = 0; i < num ; i++) begin
      drop = 0;
      derr = 0;

      `uvm_create_obj(flash_otf_item, exp_item)
      page = cfg.addr2page(tl_addr[OTFBankId:0]);
      `uvm_info("direct_readback", $sformatf("direct page: %0d", page), UVM_MEDIUM)
      my_region = cfg.get_region(page);
      flash_op.op = FlashOpRead;

      exp_item.page = page;
      exp_item.region = my_region;
      exp_item.start_addr = tl_addr;
      exp_item.addr_key = otp_addr_key;
      exp_item.data_key = otp_data_key;

      rd_entry.addr = tl_addr;
      rd_entry.addr[TL_AW-1:OTFBankId] = 0;
      // Address has to be 8byte aligned
      rd_entry.addr[2:0] = 'h0;
      rd_entry.part = FlashPartData;

        if (cfg.ecc_mode > FlashEccEnabled) begin
          if (exp_item.region.ecc_en == MuBi4True) begin
            flash_op.addr = tl_addr;
            // host can only access data partitions.
            flash_op.partition = FlashPartData;
            flash_op.num_words = 1;
            if (cfg.ecc_mode == FlashSerrTestMode || tl_addr[2] == 0) begin
              cfg.add_bit_err(flash_op, ReadTaskHost, exp_item);
            end
            if (cfg.derr_once) begin
              derr_is_set = cfg.derr_created[ReadTaskHost] & ~global_derr_is_set;
            end else begin
              derr_is_set = (cfg.derr_created[ReadTaskHost] | cfg.ierr_created[ReadTaskHost]);
            end

            if (derr_is_set) begin
              `uvm_info("direct_readback", $sformatf("assert_derr 0x%x", tl_addr), UVM_MEDIUM)
              cfg.scb_h.ecc_error_addr[{tl_addr[31:3],3'h0}] = 1;
              global_derr_is_set = 1;
            end
            if (cfg.derr_once == 0) cfg.derr_created[ReadTaskHost] = 0;
            `uvm_info("direct_readback",
                      $sformatf("ierr_created[ReadTaskHost]:%0d  derr_is_set:%0d exists:%0d",
                                cfg.ierr_created[ReadTaskHost], derr_is_set,
                                cfg.scb_h.ecc_error_addr.exists({tl_addr[31:3],3'h0})),
                      UVM_MEDIUM)
            cfg.ierr_created[ReadTaskHost] = 0;
          end
          if (cfg.scb_h.ecc_error_addr.exists({tl_addr[31:3],3'h0}) | derr_is_set) begin
            derr = 1;
          end
        end // if (cfg.ecc_mode > FlashEccEnabled)

       cfg.otf_read_entry.insert(rd_entry, flash_op);
       if (my_region.ecc_en == MuBi4True && cfg.otf_scb_h.corrupt_entry.exists(rd_entry) == 1) begin
         bit local_derr = 0;
         check_mem_intg(exp_item, bank, local_derr);
         if (local_derr) begin
           exp_item.derr = 1;
           derr = 1;
           cfg.scb_h.ecc_error_addr[{tl_addr[31:3],3'h0}] = 1;
           if (derr & cfg.scb_h.do_alert_check) begin
             cfg.scb_h.expected_alert["fatal_err"].expected = 1;
             cfg.scb_h.expected_alert["fatal_err"].max_delay = 2000;
             cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;
           end
         end
      end

      `uvm_info("direct_readback", $sformatf("idx:%0d: bank:%0d exec: 0x%x page:%0d derr:%0d",
                                             i, bank, tl_addr, page, derr), UVM_MEDIUM)
      cfg.inc_otd_tbl(bank, tl_addr, FlashPartData);
      do_direct_read(.addr(tl_addr), .mask('1), .blocking(1), .rdata(rdata),
                     .completed(completed), .exp_err_rsp(derr));

      if (completed) begin
        exp_item.dq.push_back(rdata);
        p_sequencer.eg_exp_host_port[bank].write(exp_item);
        `uvm_info("direct_readback",
                  $sformatf("SEQ:st_addr:%x addr:%x rcvd:%0d rdata:%x derr:%0d",
                            st_addr, tl_addr, cfg.otf_host_rd_rcvd, rdata, derr),
                  UVM_MEDIUM)
      end else begin
        `uvm_info("direct_readback",
                  $sformatf("SEQ:st_addr:%x addr:%x rcvd:%0d aborted  derr:%0d",
                            st_addr, tl_addr, cfg.otf_host_rd_rcvd, derr),
                  UVM_MEDIUM)
      end
      cfg.dec_otd_tbl(bank, tl_addr, FlashPartData);
      cfg.otf_host_rd_rcvd++;
      tl_addr += 4;
     end // for (int i = 0; i < num ; i++)


   endtask

   task erase_flash(flash_op_t flash_op, int bank, bit in_err = 0);
     bit drop = 0;
     int page;
     flash_mp_region_cfg_t my_region;

     flash_op.op = FlashOpErase;
     flash_op.addr[TL_AW-1:OTFBankId] = bank;
     flash_op.otf_addr = flash_op.addr;
     flash_op.erase_type = FlashErasePage;

     if (cfg.ecc_mode > FlashEccEnabled) begin
       if (flash_op.partition == FlashPartData) begin
         flash_op.otf_addr[18:17] = cfg.tgt_pre[flash_op.partition][TgtEr];
       end else begin
         flash_op.otf_addr[10:9] = cfg.tgt_pre[flash_op.partition][TgtEr];
       end
     end
     `uvm_info("erase_flash", $sformatf("{bank:%0d otf_addr:0x%0h, page:%0d part:%s erase_type:%s",
                                        bank, flash_op.otf_addr, cfg.addr2page(flash_op.addr),
                                        flash_op.partition.name, flash_op.erase_type.name),
               UVM_MEDIUM)
     if (flash_op.partition == FlashPartData) begin
       page = cfg.addr2page(flash_op.addr);
       my_region = cfg.get_region(page);
     end else begin
       page = cfg.addr2page(flash_op.otf_addr);
       my_region = cfg.get_region_from_info(cfg.mp_info[bank][flash_op.partition>>1][page]);
       drop = check_info_part(flash_op, "erase_flash");
     end
     drop |= validate_flash_op(flash_op, my_region);
     if (drop) begin
       `uvm_info("erase_flash", $sformatf("op:%s is not allowed in this region %p",
                                          flash_op.op.name, my_region), UVM_MEDIUM)
       set_otf_exp_alert("recov_err");
     end
     flash_ctrl_start_op(flash_op);
     if (!in_err) wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
   endtask

  // Update rd / dr tgt of the memory with their page profile
  virtual function void flash_otf_mem_read_zone_init();
    // 8byte aligned
    addr_t st_addr, ed_addr;
    flash_dv_part_e part;
    // read tgt region     : cfg.tgt_pre[0]
    // direct rd tgt region: cfg.tgt_pre[1]
    part = part.first;
    do begin
      for (flash_tgt_prefix_e j = TgtRd; j <= TgtDr; j = j.next()) begin
        st_addr = 'h0;
        if (part == FlashPartData) begin
          st_addr[18:17] = cfg.tgt_pre[part][j];
          // I think this should be
          // 64 * 256 * 8 -1 (= 0x1_FFFF)
          // to maxout a quater of 1 bank
          // Will be address the next PR
          ed_addr = st_addr + 64 * 255 * 8; // + 0x1_FE00
          // data partition 2 banks
          for (int i = 0; i < 2; i++) begin
            for (addr_t addr = st_addr; addr <= ed_addr; addr += 8) begin
              cfg.update_otf_mem_read_zone(part, i, addr);
            end
            `uvm_info("flash_otf_init",
                      $sformatf("part:%s pre:%s bank:%0d st:%x ed:%x",
                                part.name, j.name, i, st_addr, ed_addr), UVM_MEDIUM)
          end
        end else begin // if (part == FlashPartData)
          // While data part can be divided by pages, info part
          // need finer resolution due to number of pages in each info
          // is relatively small.
          // So every page in info part will be divided into 4 parts.
          st_addr[10:9] = cfg.tgt_pre[part][j];
          for (int k = 0; k < InfoTypeSize[part>>1]; k++) begin
            st_addr[DVPageMSB:DVPageLSB] = k; // page
            ed_addr = st_addr + 511; // 0x1FF
            for (int i = 0; i < 2; i++) begin
              for (addr_t addr = st_addr; addr <= ed_addr; addr += 8) begin
                cfg.update_otf_mem_read_zone(part, i, addr);
              end
            end
            `uvm_info("flash_otf_init",
                      $sformatf("part:%s pre%0d page:%0d st:%x ed:%x",
                                part.name, j, k, st_addr, ed_addr), UVM_MEDIUM)
          end
        end
      end // for (int j = TgtRd; j <= TgtDr; j++)
      part = part.next;
    end while (part != part.first);

  endfunction // flash_otf_init

  // Send direct host read to both banks 'host_num' times.
  virtual task send_rand_host_rd(int num = -1, bit in_err = 0);
    flash_op_t host;
    int host_num, host_bank;

    host.otf_addr[OTFHostId-2:0] = $urandom();
    host.otf_addr[1:0] = 'h0;
    if (num >= 0) host_num = num;
    else host_num = $urandom_range(1,32);
    host_bank = $urandom_range(0,1);

    `uvm_info(`gfn, $sformatf(
              "send_rand_host_rd addr=0x%x bank=%0d host_num=%0d, in_err=%b",
              host.otf_addr, host_bank, host_num, in_err), UVM_MEDIUM)
    otf_direct_read(host.otf_addr, host_bank, host_num, in_err);
  endtask // send_rand_host_rd

  // Clean up tb vars. Used for multiple sequence run.
  task otf_tb_clean_up();
    cfg.scb_h.alert_count["fatal_err"] = 0;
    cfg.scb_h.exp_alert_contd["fatal_err"] = 0;
    cfg.scb_h.alert_count["recov_err"] = 0;
    cfg.scb_h.exp_alert_contd["recov_err"] = 0;
    cfg.scb_h.eflash_addr_phase_queue = '{};

    cfg.derr_addr_tbl.delete();
    cfg.derr_created = '{default: ReadTaskCtrl};
    cfg.serr_addr_tbl.delete();
    cfg.derr_otd.delete();

    cfg.scb_h.ecc_error_addr.delete();
    cfg.scb_h.in_error_addr.delete();
    global_derr_is_set = 0;

    cfg.otf_scb_h.stop = 1;
    cfg.otf_read_entry.hash.delete();
    foreach (cfg.otf_read_entry.prv_read[i]) cfg.otf_read_entry.prv_read[i] = '{};
    cfg.otf_scb_h.clear_fifos();

    for (int i = 0; i < NumBanks; i++) begin
      cfg.otf_scb_h.data_mem[i].delete();
      foreach (cfg.otf_scb_h.info_mem[i][j])
        cfg.otf_scb_h.info_mem[i][j].delete();
    end
  endtask // otf_tb_clean_up

  // Populate cfg.mp_info with default_info_page_cfg except scr, ecc.
  // Then program each info region.
  virtual task flash_ctrl_default_info_cfg(otf_cfg_mode_e scr_mode = OTFCfgFalse,
                                   otf_cfg_mode_e ecc_mode = OTFCfgFalse);
    mubi4_t scr_en, ecc_en;
    // If scr/ecc mode is random,
    // follow rand_info_c
    scr_en = get_mubi_val(scr_mode);
    ecc_en = get_mubi_val(ecc_mode);

    foreach (cfg.mp_info[i, j, k]) begin
      if (cfg.ecc_mode == FlashEccDisabled) cfg.mp_info[i][j][k] = cfg.default_info_page_cfg;
      else cfg.mp_info[i][j][k] = rand_info[i][j][k];
      if (scr_mode != OTFCfgRand) cfg.mp_info[i][j][k].scramble_en = scr_en;
      if (ecc_mode != OTFCfgRand) cfg.mp_info[i][j][k].ecc_en = ecc_en;

      // overwrite secret_partition cfg with hw_cfg0
      cfg.mp_info[0][0][1] = conv2env_mp_info(flash_ctrl_pkg::CfgAllowRead);
      cfg.mp_info[0][0][2] = conv2env_mp_info(flash_ctrl_pkg::CfgAllowRead);

      flash_ctrl_mp_info_page_cfg(i, j, k, cfg.mp_info[i][j][k]);
      `uvm_info("otf_info_cfg", $sformatf("bank:type:page:[%0d][%0d][%0d] = %p",
                                          i, j, k, cfg.mp_info[i][j][k]), UVM_MEDIUM)
    end
    // Add callback to customize mp info
    callback_vseq.update_env_mp_info();
  endtask // flash_ctrl_default_info_cfg

  virtual task flash_otf_region_cfg(otf_cfg_mode_e scr_mode = OTFCfgFalse,
                                    otf_cfg_mode_e ecc_mode = OTFCfgFalse);
    mubi4_t scr_en, ecc_en;
    // If scr/ecc mode is random,
    // follow rand_regions_c
    scr_en = get_mubi_val(scr_mode);
    ecc_en = get_mubi_val(ecc_mode);

    flash_ctrl_default_region_cfg(,,,scr_en, ecc_en);
    foreach (cfg.mp_regions[i]) begin
      cfg.mp_regions[i] = rand_regions[i];
      // use default region in FlashEccDisabled mode.
      if (cfg.ecc_mode == FlashEccDisabled) cfg.mp_regions[i].en = MuBi4False;
      if (scr_mode != OTFCfgRand) cfg.mp_regions[i].scramble_en = scr_en;
      if (ecc_mode != OTFCfgRand) cfg.mp_regions[i].ecc_en = ecc_en;

      flash_ctrl_mp_region_cfg(i, cfg.mp_regions[i]);
      `uvm_info("otf_region_cfg", $sformatf("region[%0d] = %p", i, cfg.mp_regions[i]), UVM_MEDIUM)
    end
    `uvm_info("otf_region_cfg", $sformatf("default = %p", cfg.default_region_cfg), UVM_MEDIUM)
    flash_ctrl_default_info_cfg(scr_mode, ecc_mode);
    update_p2r_map(cfg.mp_regions);
  endtask // flash_otf_region_cfg

  task send_rand_ops(int iter = 1, bit exp_err = 0, bit ctrl_only = 0);
    flash_op_t ctrl;
    int num, bank;
    int host_pct = (ctrl_only)? 0 : 1;

    repeat (iter) begin
      randcase
        1: begin
          `DV_CHECK(try_create_prog_op(ctrl, bank, num), "Could not create a prog flash op")
          prog_flash(ctrl, bank, 1, fractions, exp_err);
        end
        1: begin
          set_ecc_err_target(TgtRd);
          `DV_CHECK_RANDOMIZE_FATAL(this)
          ctrl = rand_op;
          get_bank_and_num(ctrl, bank, num);
          read_flash(ctrl, bank, 1, fractions, 0, exp_err);
        end
        host_pct: send_rand_host_rd(.in_err(exp_err));
        1: begin
          set_ecc_err_target(TgtEr);
          `DV_CHECK_RANDOMIZE_FATAL(this)
          ctrl = rand_op;
          get_bank_and_num(ctrl, bank, num);
          erase_flash(ctrl, bank, exp_err);
        end
      endcase // randcase
    end
  endtask

  // Use this task only after flash is disabled.
  task flash_access_after_disabled();
    `uvm_info(`gfn, "Flash Access after disabled", UVM_LOW)
    cfg.m_tl_agent_cfg.check_tl_errs = 0;
    send_rand_ops(.iter(5), .exp_err(1), .ctrl_only(1));

    // Disable tlul_err_cnt check
    cfg.tlul_core_obs_cnt = cfg.tlul_core_exp_cnt;
  endtask // flash_access_after_disabled

  function void update_partition_access(bit[2:0] acc);
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::Off;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::Off;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::Off;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::Off;

    if (acc[0]) cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    if (acc[1]) cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en = lc_ctrl_pkg::On;
    if (acc[2]) begin
      cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en = lc_ctrl_pkg::On;
      cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en = lc_ctrl_pkg::On;
    end
  endfunction // update_partition_access

  function mubi4_t get_mubi_val(otf_cfg_mode_e mode);
    case (mode)
      OTFCfgRand: begin
        // return true or false with 1:1 ratio
        return get_rand_mubi4_val(.other_weight(0));
      end
      OTFCfgTrue: return MuBi4True;
      default: return MuBi4False;
    endcase
  endfunction // get_mubi_val

  function flash_dv_part_e get_dv_part_from_int(int page);
    if (page < 1000) return FlashPartData;
    else begin
      if (page < 1010) begin
        return FlashPartInfo;
      end else if (page < 1011) begin
        return FlashPartInfo1;
      end
    end
    return FlashPartInfo2;
  endfunction // get_dv_part_from_int

  // return right page number from 1000+ number
  function int get_info_page(flash_dv_part_e info, int num);
    int page;
    case (info)
      FlashPartInfo: page = num - 1000;
      FlashPartInfo1: page = num - 1010;
      FlashPartInfo2: page = num - 1011;
      default: `uvm_error("get_info_page", $sformatf("%s is not valid info page",
                                                     info.name))
    endcase // case (info)
    return page;
  endfunction // get_info_page

  // Write all 1 to secret partition for some write tests.
  function void flash_otf_set_secret_part();
    int page = 1;
    repeat(2) begin
      int page_st_addr = page*2048;
      uvm_hdl_data_t data = '{default:1};
      for (int addr = page_st_addr; addr < (page_st_addr + 8*256); addr += 8) begin
        cfg.mem_bkdr_util_h[FlashPartInfo][0].write(addr, data);
      end
      page++;
    end
  endfunction

  // Do backdoor read and check if double error exists.
  task check_mem_intg(flash_otf_item exp, int bank, ref bit err);
    flash_otf_item obs;
    `uvm_create_obj(flash_otf_item, obs)

    obs.cmd.partition = FlashPartData;
    obs.cmd.op = FlashOpRead;
    obs.cmd.addr = exp.start_addr; // tl_addr
    // for debug print
    obs.start_addr = exp.start_addr;
    obs.cmd.num_words = 1;
    obs.mem_addr = exp.start_addr >> 3;

    cfg.flash_mem_otf_read(obs.cmd, obs.fq);

    obs.print("chk_mem_intg: before");
    obs.region = exp.region;
    obs.skip_err_chk = 1;

    // descramble needs 2 buswords
    obs.cmd.num_words = 2;
    obs.descramble(exp.addr_key, exp.data_key);
    obs.print("chk_mem_intg: after");
    err = obs.derr;
  endtask
endclass // flash_ctrl_otf_base_vseq
