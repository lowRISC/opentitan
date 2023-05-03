// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is base class for on the fly mode test sequence.
// On the fly mode test checks data integrity per transaction (program or read),
// and doesn't rely on reference memory model in the test bench.
class flash_ctrl_otf_base_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_otf_base_vseq)
  `uvm_object_new

  // Used for tracing programmed data
  bit [15:0] global_pat_cnt = 16'hA000;

  // Double bit err is created
  bit        global_derr_is_set = 0;

  // Trace host read ountstanding
  int        d_cnt1, d_cnt2;

  // Number of controller transactions per a single task
  // Min: 1 Max:32
  rand int  ctrl_num;
  rand int  ctrl_info_num;
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
  constraint ctrl_num_c {
    ctrl_num dist { CTRL_TRANS_MIN := 2, [2:31] :/ 1, CTRL_TRANS_MAX := 2};
  }
  constraint fractions_c {
    fractions dist { [1:4] := 4, [5:15] := 1, 16 := 1};
  }
  constraint ctrl_info_num_c {
    solve rand_op before ctrl_info_num;
    ctrl_info_num inside {[1 : InfoTypeSize[rand_op.partition >> 1]]};
    if (cfg.ecc_mode > FlashEccEnabled) ctrl_info_num * fractions <= 128;
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
    // If address starts from 0x4 and full prog_win size access(16),
    // transaction creates prog_win error.
    // To prevent that, make full size access always start from address[2:0] == 0.
    if (fractions == 16) rand_op.addr[2] == 0;
    if (rand_op.partition != FlashPartData) {
      rand_op.addr inside {[0:InfoTypeBytes[rand_op.partition>>1]-1]};
      rand_op.prog_sel == 1;
    } else {
      rand_op.prog_sel == 0;
    }
    rand_op.otf_addr == rand_op.addr[BusAddrByteW-2:0];
    rand_op.num_words inside {[1:16]};
    rand_op.addr[5:0] + ((rand_op.num_words - 1) * 4) < 64;
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

    // overwrite secret_partition cfg with hw_cfg
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
        flash_ctrl_intr_enable(6'h3f);
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

  // Program flash in the unit of minimum resolution (4Byte)
  // If data is not aligned to 8Byte, rtl pads all F to
  // upper or lower 4Byte.
  // @arg: flash_op_p : command struct return updated address after write
  // @arg: bank: bank index to access flash
  // @arg: num : number of 8 words range: [1 : 32]
  // @arg: wd  : number of 4byte (TL bus unit) : default : 16
  // @arg: in_err : inject fatal error causes flash access disable
  task prog_flash(ref flash_op_t flash_op, input int bank, int num, int wd = 16,
                  bit in_err = 0, bit store_prog_data = 0);
    data_q_t flash_data_chunk;
    flash_otf_item exp_item;
    bit poll_fifo_status = ~in_err;
    bit [15:0] lcnt = 0;
    bit [flash_ctrl_pkg::BusAddrByteW-1:0] start_addr, end_addr;
    data_4s_t tmp_data;
    int tail, is_odd;
    int unit_word;
    int tot_wd;
    int page;
    bit overflow = 0;
    bit drop = 0;

    flash_mp_region_cfg_t my_region;

    is_odd = flash_op.otf_addr[2];
    tot_wd = wd * num + is_odd;

    flash_op.op = FlashOpProgram;
    flash_op.num_words = wd;

    if (cfg.ecc_mode > FlashEccEnabled) begin
      if (flash_op.partition == FlashPartData) begin
        flash_op.otf_addr[18:17] = cfg.tgt_pre[flash_op.partition][TgtWr];
      end else begin
        flash_op.otf_addr[10:9] = cfg.tgt_pre[flash_op.partition][TgtWr];
      end
    end

    start_addr = flash_op.otf_addr;
    // last byte address in each program
    end_addr = start_addr + (tot_wd * 4) - 1;

    `uvm_info("prog_flash",$sformatf("begin addr:%x part:%s num:%0d wd:%0d st:%x ed:%x",
                                     flash_op.otf_addr, flash_op.partition.name, num,
                                     wd, start_addr, end_addr), UVM_MEDIUM)

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
      bit [flash_ctrl_pkg::BusAddrByteW-1:0] tmp_addr = start_addr;
      if (flash_op.partition == FlashPartData) begin
        start_addr[16:0] = 'h0;
      end else begin
        start_addr[8:0] = 'h0;
      end
      `uvm_info("prog_flash", $sformatf({"overflow!, start:%x end:%x part:%s",
                                         " roll over start address to 0x%x"},
                                        tmp_addr, end_addr, flash_op.partition.name,
                                        start_addr), UVM_MEDIUM)
      is_odd = flash_op.otf_addr[2];
      tot_wd = wd * num + is_odd;
      end_addr = start_addr + (tot_wd * 4) - 1;
    end
    // Check if end_addr overflows.
    // Roll over start address if this is the case.
    `uvm_info("prog_flash", $sformatf({"bank:%0d otf_addr:0x%0h,",
                                       " part:%s size:%0d x %0d x 4B"},
                                      bank, flash_op.otf_addr, flash_op.partition.name,
                                      num, wd), UVM_MEDIUM)
    flash_op.otf_addr = start_addr;

    for (int i = 0; i < num; i++) begin
      flash_program_data = '{};
      tail = 0;
      drop = 0;
      is_odd = flash_op.otf_addr[2];
      end_addr = flash_op.otf_addr + ((wd + is_odd) * 4) - 1;
      // Check resolution error
      // Current resolution : 0x40.
      // Check if address[6] is same for start and end addr.
      `uvm_info("prog_flash", $sformatf("start_addr:%x  end_addr:%x",
                                        flash_op.otf_addr, end_addr), UVM_HIGH)
      if (flash_op.otf_addr[6] != end_addr[6]) begin
        `uvm_info("prog_flash", $sformatf("prog_window violation, start_addr:0x%x  end_addr:0x%x",
                                          flash_op.otf_addr, end_addr), UVM_MEDIUM)
        // Shift start addr window
        if (flash_op.partition == FlashPartData) begin
          flash_op.otf_addr[BusAddrByteW-1:6] = end_addr[BusAddrByteW-1:6];
          flash_op.otf_addr[5:0] = 0;
        end else begin
          flash_op.otf_addr[8:0] = 'h0;
        end
        end_addr = flash_op.otf_addr + (wd * 4) -1;
        `uvm_info("prog_flash", $sformatf("change to page:%0d start_addr to 0x%x end_addr:0x%x",
                                          cfg.addr2page(flash_op.addr),
                                          flash_op.otf_addr,
                                          end_addr), UVM_MEDIUM)
        is_odd = 0;
      end
      unit_word = wd;
      // Each flash_program_data[] entry : 4B
      // {global_cnt(16bits), lcnt(16bits)}
      for (int j = 0; j < wd; j++) begin
        if (cfg.wr_rnd_data) begin
           flash_program_data.push_back($urandom);
        end else begin
           flash_program_data.push_back({global_pat_cnt, lcnt++});
        end
      end
      flash_op.addr = flash_op.otf_addr;
      // Bank : bit[19]
      flash_op.addr[TL_AW-1:OTFBankId] = bank;

      if (flash_op.partition == FlashPartData) begin
        page = cfg.addr2page(flash_op.addr);
        my_region = cfg.get_region(page);
      end else begin
        // for region, use per bank page number
        page = cfg.addr2page(flash_op.otf_addr);
        my_region = cfg.get_region_from_info(cfg.mp_info[bank][flash_op.partition>>1][page]);
        drop = check_info_part(flash_op, "prog_flash");
      end

      drop |= validate_flash_op(flash_op, my_region);
      if (drop) begin
        `uvm_info("prog_flash", $sformatf("op:%s is not allowed in this region %p",
                                          flash_op.op.name, my_region), UVM_MEDIUM)
        set_otf_exp_alert("recov_err");
      end

      if (cfg.intr_mode) begin
        flash_ctrl_intr_write(flash_op, flash_program_data);
      end else begin
        flash_ctrl_start_op(flash_op);
        if (in_err) begin
          cfg.tlul_core_exp_cnt += flash_op.num_words;
        end
        flash_ctrl_write(flash_program_data, poll_fifo_status);

        if (!in_err) wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
      end
      if (is_odd == 1) begin
        tmp_data = {32{1'b1}};
        flash_program_data.push_front(tmp_data);
        unit_word++;
      end
      tail = unit_word % 2;

      if (wd > 1 && tail == 1) begin
        tmp_data = {32{1'b1}};
        flash_program_data.push_back(tmp_data);
      end
      if (wd == 1 && is_odd == 0) begin
        tmp_data = {32{1'b1}};
        flash_program_data.push_back(tmp_data);
      end
      if (wd > 16) begin
        csr_rd_check(.ptr(ral.err_code.prog_win_err), .compare_value(1));
        drop = 1;
      end
      `uvm_info("prog_flash",$sformatf({"bank:%0d addr:%x otf_addr:%x part:%s",
                                        " page:%0d num:%0d wd:%0d  odd:%0d tail:%0d"},
                                        bank, flash_op.addr, flash_op.otf_addr,
                                        flash_op.partition.name, page, num,
                                        wd, is_odd, tail), UVM_MEDIUM)
      if (drop) begin
        uvm_reg_data_t ldata;
        csr_rd(.ptr(ral.err_code), .value(ldata), .backdoor(1));
        `uvm_info("prog_flash", $sformatf("skip sb path due to err_code:%x", ldata), UVM_MEDIUM)
      end else begin
        if (store_prog_data) cfg.prog_data[flash_op] = flash_program_data;

        flash_otf_print_data64(flash_program_data, "wdata");
        `uvm_create_obj(flash_otf_item, exp_item)

        exp_item.cmd = flash_op;
        exp_item.dq = flash_program_data;
        exp_item.region = my_region;
        // Scramble data
        exp_item.scramble(otp_addr_key, otp_data_key, flash_op.otf_addr);

        p_sequencer.eg_exp_ctrl_port[bank].write(exp_item);
        flash_phy_prim_agent_pkg::print_flash_data(exp_item.fq,
              $sformatf("fdata_%0d bank%0d", cfg.otf_ctrl_wr_sent, bank));
      end
      flash_op.otf_addr = flash_op.otf_addr + (4 * wd);
      global_pat_cnt++;
      cfg.otf_ctrl_wr_sent++;
    end // for (int i = 0; i < num; i++)
  endtask // prog_flash

  // Read flash in the unit of minimum resolution (4 Byte).
  // 1 word : 8Byte
  // @arg: flash_op_p : command struct return updated address after write
  // @arg: bank: bank index to access flash
  // @arg: num : number of 8 words range: [1 : 32]
  // @arg: wd  : number of 4byte (TL bus unit) : default : 16
  // @arg: overrd : invoke oversize read
  // @arg: in_err : inject fatal error causes flash access disable
  task read_flash(ref flash_op_t flash_op, input int bank, int num, int wd = 16,
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
    if (cfg.ecc_mode > FlashEccEnabled) begin
      if (flash_op.partition == FlashPartData) begin
        flash_op.otf_addr[18:17] = cfg.tgt_pre[flash_op.partition][TgtRd];
      end else begin
        flash_op.otf_addr[10:9] = cfg.tgt_pre[flash_op.partition][TgtRd];
      end
    end else begin
      flash_op.otf_addr[OTFHostId] = 0;
    end

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
      if (cfg.ecc_mode > FlashEccEnabled) begin
        if (flash_op.partition == FlashPartData) begin
          flash_op.otf_addr[18:17] = cfg.tgt_pre[flash_op.partition][TgtRd];
        end else begin
          flash_op.otf_addr[10:9] = cfg.tgt_pre[flash_op.partition][TgtRd];
        end
      end
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
      exp_item.data_key=  otp_data_key;

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
        derr_is_set = cfg.derr_created[0] & ~global_derr_is_set;
      end else begin
        derr_is_set = cfg.derr_created[0];
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
      if (derr_is_set | cfg.ierr_created[0]) begin
        `uvm_info("read_flash", $sformatf({"bank:%0d addr: %x(otf:%x) derr_is_set:%0d",
                                          " ierr_created[0]:%0d"}, bank, flash_op.addr,
                                          flash_op.otf_addr, derr_is_set, cfg.ierr_created[0])
                  , UVM_MEDIUM)
        csr_rd_check(.ptr(ral.op_status.err), .compare_value(1));
        csr_rd_check(.ptr(ral.err_code.rd_err), .compare_value(1));
        reg_data = get_csr_val_with_updated_field(ral.err_code.rd_err, reg_data, 1);
        csr_wr(.ptr(ral.err_code), .value(reg_data));
        reg_data = get_csr_val_with_updated_field(ral.op_status.err, reg_data, 0);
        csr_wr(.ptr(ral.op_status), .value(reg_data));
        if (cfg.derr_once == 0) cfg.derr_created[0] = 0;
        cfg.ierr_created[0] = 0;
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
  task otf_direct_read(bit [OTFHostId-2:0] addr, int bank, int num, bit in_err);
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
    `uvm_info("direct_read", $sformatf("addr: %x end_addr: %x overflow:% x",
                                       addr, end_addr, overflow), UVM_HIGH)
    rd_entry.bank = bank;
    tl_addr[OTFBankId] = bank;
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
      exp_item.data_key=  otp_data_key;

      // Address should be per bank addr
      rd_entry.addr = tl_addr;
      rd_entry.addr[OTFBankId] = 0;

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
            derr_is_set = cfg.derr_created[1] & ~global_derr_is_set;
          end else begin
            derr_is_set = (cfg.derr_created[1] | cfg.ierr_created[1]);
          end

          if (derr_is_set) begin
            `uvm_info("direct_read", $sformatf("assert_derr 0x%x", tl_addr), UVM_MEDIUM)
            cfg.scb_h.ecc_error_addr[{tl_addr[31:3],3'h0}] = 1;
            global_derr_is_set = 1;
          end
          if (cfg.derr_once == 0) cfg.derr_created[1] = 0;
          `uvm_info("direct_read", $sformatf("ierr_created[1]:%0d  derr_is_set:%0d exists:%0d",
                                   cfg.ierr_created[1], derr_is_set,
                                   cfg.scb_h.ecc_error_addr.exists({tl_addr[31:3],3'h0})),
                                   UVM_MEDIUM)
          cfg.ierr_created[1] = 0;
        end
        if (cfg.scb_h.ecc_error_addr.exists({tl_addr[31:3],3'h0}) | derr_is_set) derr = 1;
      end
      cfg.otf_read_entry.insert(rd_entry, flash_op);
      `uvm_info("direct_read", $sformatf("num_i:%0d bank:%0d exec: 0x%x derr:%0d in_err:%0d",
                                          i, bank, tl_addr, derr, in_err), UVM_MEDIUM)
      if (in_err) cfg.scb_h.in_error_addr[{tl_addr[31:3],3'h0}] = 1;

      derr |= in_err;

      if (cfg.ecc_mode > FlashSerrTestMode) begin
        if (derr & cfg.scb_h.do_alert_check) begin
          cfg.scb_h.expected_alert["fatal_err"].expected = 1;
          cfg.scb_h.expected_alert["fatal_err"].max_delay = 2000;
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
        exp_item.ctrl_rd_region_q.push_back(my_region);
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
      exp_item.addr_key = otp_addr_key;
      exp_item.data_key=  otp_data_key;

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

      if (derr_is_set | cfg.ierr_created[0]) begin
        uvm_reg_data_t ldata;
        csr_rd(.ptr(ral.err_code), .value(ldata), .backdoor(1));
        `uvm_info("readback_flash", $sformatf({"bank:%0d addr: %x(otf:%x) derr_is_set:%0d",
                                          " ierr_created[0]:%0d"}, bank, flash_op.addr,
                                          flash_op.otf_addr, derr_is_set, cfg.ierr_created[0])
                  , UVM_MEDIUM)
        csr_rd_check(.ptr(ral.op_status.err), .compare_value(1));
        csr_rd_check(.ptr(ral.err_code.rd_err), .compare_value(1));
        reg_data = get_csr_val_with_updated_field(ral.err_code.rd_err, reg_data, 1);
        csr_wr(.ptr(ral.err_code), .value(reg_data));
        reg_data = get_csr_val_with_updated_field(ral.op_status.err, reg_data, 0);
        csr_wr(.ptr(ral.op_status), .value(reg_data));
        if (cfg.derr_once == 0) cfg.derr_created[0] = 0;
        cfg.ierr_created[0] = 0;
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
    tl_addr[OTFBankId] = bank;
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
      exp_item.data_key=  otp_data_key;

      rd_entry.addr = tl_addr;
      rd_entry.addr[OTFBankId] = 0;
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
            derr_is_set = cfg.derr_created[1] & ~global_derr_is_set;
          end else begin
            derr_is_set = (cfg.derr_created[1] | cfg.ierr_created[1]);
          end

          if (derr_is_set) begin
            `uvm_info("direct_readback", $sformatf("assert_derr 0x%x", tl_addr), UVM_MEDIUM)
            cfg.scb_h.ecc_error_addr[{tl_addr[31:3],3'h0}] = 1;
            global_derr_is_set = 1;
          end
          if (cfg.derr_once == 0) cfg.derr_created[1] = 0;
          `uvm_info("direct_readback", $sformatf("ierr_created[1]:%0d  derr_is_set:%0d exists:%0d",
                                   cfg.ierr_created[1], derr_is_set,
                                   cfg.scb_h.ecc_error_addr.exists({tl_addr[31:3],3'h0})),
                                   UVM_MEDIUM)
          cfg.ierr_created[1] = 0;
        end
        if (cfg.scb_h.ecc_error_addr.exists({tl_addr[31:3],3'h0}) | derr_is_set) derr = 1;
        end
      cfg.otf_read_entry.insert(rd_entry, flash_op);
      if (my_region.ecc_en == MuBi4True && cfg.otf_scb_h.corrupt_entry.exists(rd_entry) == 1) begin
        exp_item.derr = 1;
        derr = 1;
         cfg.scb_h.ecc_error_addr[{tl_addr[31:3],3'h0}] = 1;
        if (derr & cfg.scb_h.do_alert_check) begin
          cfg.scb_h.expected_alert["fatal_err"].expected = 1;
          cfg.scb_h.expected_alert["fatal_err"].max_delay = 2000;
          cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;
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
     flash_op.otf_addr[OTFBankId] = bank;
     flash_op.addr = flash_op.otf_addr;
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
  function void flash_otf_mem_read_zone_init();
    // 8byte aligned
    addr_t st_addr, ed_addr;
    flash_dv_part_e part;
    // read tgt region     : cfg.tgt_pre[0]
    // direct rd tgt region: cfg.tgt_pre[1]
    part = part.first;
    do begin
      for (flash_tgt_prefix_e j = TgtRd; j <= TgtDr; j++) begin
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

  // Send direct host read to both bankds 'host_num' times.
  virtual task send_rand_host_rd(int num = -1, bit in_err = 0);
    flash_op_t host;
    int host_num, host_bank;

    host.otf_addr[OTFHostId-2:0] = $urandom();
    host.otf_addr[1:0] = 'h0;
    if (num >= 0) host_num = num;
    else host_num = $urandom_range(1,128);
    host_bank = $urandom_range(0,1);

    otf_direct_read(host.otf_addr, host_bank, host_num, in_err);
  endtask // send_rand_host_rd

  // Clean up tb vars. Used for multiple sequence run.
  task otf_tb_clean_up();
    cfg.scb_h.alert_count["fatal_err"] = 0;
    cfg.scb_h.exp_alert_contd["fatal_err"] = 0;
    cfg.scb_h.alert_count["recov_err"] = 0;
    cfg.scb_h.exp_alert_contd["recov_err"] = 0;
    cfg.scb_h.eflash_addr_phase_queue = '{};

    cfg.derr_created[0] = 0;
    cfg.derr_created[1] = 0;
    cfg.derr_addr_tbl.delete();
    cfg.derr_otd.delete();
    cfg.serr_addr_tbl.delete();

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

      // overwrite secret_partition cfg with hw_cfg
      cfg.mp_info[0][0][1] = conv2env_mp_info(flash_ctrl_pkg::CfgAllowRead);
      cfg.mp_info[0][0][2] = conv2env_mp_info(flash_ctrl_pkg::CfgAllowRead);

      // Add callback to customize mp info
      callback_vseq.update_env_mp_info();

      flash_ctrl_mp_info_page_cfg(i, j, k, cfg.mp_info[i][j][k]);
      `uvm_info("otf_info_cfg", $sformatf("bank:type:page:[%0d][%0d][%0d] = %p",
                                          i, j, k, cfg.mp_info[i][j][k]), UVM_MEDIUM)
    end
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
      `DV_CHECK_RANDOMIZE_FATAL(this)
      ctrl = rand_op;
      bank = rand_op.addr[OTFBankId];
      if (ctrl.partition == FlashPartData) begin
        num = ctrl_num;
      end else begin
        num = ctrl_info_num;
      end
      randcase
        1: prog_flash(ctrl, bank, 1, fractions, exp_err);
        1: read_flash(ctrl, bank, 1, fractions, 0, exp_err);
        host_pct: send_rand_host_rd(.in_err(exp_err));
        1: erase_flash(ctrl, bank, exp_err);
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

endclass // flash_ctrl_otf_base_vseq
