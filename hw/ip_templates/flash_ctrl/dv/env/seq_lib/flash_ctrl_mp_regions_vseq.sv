// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Memory protect test. Overlapping regions with randomization.
// Send one op among program, read and erase (page) in each trans round.
// This sequence uses local mp_region db. Don't use cfg.get_region()
class flash_ctrl_mp_regions_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_mp_regions_vseq)

  `uvm_object_new

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();

    // set page erase as default
    cfg.seq_cfg.op_erase_type_bank_pc          = 0;

    // enable high endurance
    cfg.seq_cfg.mp_region_he_en_pc             = 50;
    cfg.seq_cfg.default_region_he_en_pc        = 50;
  endfunction

  rand flash_op_t flash_op;
  flash_op_t      flash_op_pg_erase;
  flash_op_t      flash_op_bk_erase;

  data_b_t set_val;

  bit     poll_fifo_status;
  bit     illegal_trans = 0;
  int     trans_cnt = 0;
  int     exp_alert_cnt = 0;

  // Memory protection regions settings.
  rand flash_mp_region_cfg_t mp_regions[flash_ctrl_pkg::MpRegions];
  // Information partitions memory protection pages settings.
  rand
  flash_bank_mp_info_page_cfg_t
  mp_info_pages[NumBanks][flash_ctrl_pkg::InfoTypes][$];

  constraint solv_order_c {
    solve mp_regions, mp_info_pages before flash_op;
  }
  // Constraint address to be in relevant range for the selected partition.
  constraint addr_c {
    if (flash_op.partition != FlashPartData) {
      flash_op.addr inside
       {[0:InfoTypeBytes[flash_op.partition>>1]-1],
        [BytesPerBank:BytesPerBank+InfoTypeBytes[flash_op.partition>>1]-1]};
    }
  }

  constraint flash_op_c {
    flash_op.op inside {FlashOpRead, FlashOpProgram, FlashOpErase};
    flash_op.addr inside {[0 : FlashSizeBytes - 1]};
    flash_op.otf_addr == flash_op.addr[OTFHostId-1:0];
    // Bank erase is supported only for data & 1st info partitions
    flash_op.partition != FlashPartData && flash_op.partition != FlashPartInfo ->
    flash_op.erase_type == flash_ctrl_pkg::FlashErasePage;

    flash_op.erase_type dist {
      flash_ctrl_pkg::FlashErasePage :/ (100 - cfg.seq_cfg.op_erase_type_bank_pc),
      flash_ctrl_pkg::FlashEraseBank :/ cfg.seq_cfg.op_erase_type_bank_pc
    };

    flash_op.num_words inside {[10 : FlashNumBusWords - flash_op.addr[TL_AW-1:TL_SZW]]};
    flash_op.num_words <= cfg.seq_cfg.op_max_words;
    flash_op.num_words < FlashPgmRes - flash_op.addr[TL_SZW+:FlashPgmResWidth];
  }

  constraint mp_regions_c {

    foreach (mp_regions[i]) {

      mp_regions[i].scramble_en == MuBi4False;

      mp_regions[i].ecc_en == MuBi4False;

      mp_regions[i].he_en dist {
        MuBi4False :/ (100 - cfg.seq_cfg.mp_region_he_en_pc),
        MuBi4True  :/ cfg.seq_cfg.mp_region_he_en_pc
      };

      mp_regions[i].start_page dist {
        0                       :/ 10,
        [1 : FlashNumPages - 2] :/ 80,
        FlashNumPages - 1       :/ 10
      };
      mp_regions[i].num_pages inside {[1 : FlashNumPages - mp_regions[i].start_page]};
      mp_regions[i].num_pages <= cfg.seq_cfg.mp_region_max_pages;
    }
  }

  constraint mp_info_pages_c {

    foreach (mp_info_pages[i]) {
      if (cfg.seq_cfg.op_readonly_on_info_partition) {
        foreach (mp_info_pages[i][0][k]) {
          mp_info_pages[i][0][k].program_en == MuBi4False;
          mp_info_pages[i][0][k].erase_en == MuBi4False;
        }
      }
      if (cfg.seq_cfg.op_readonly_on_info1_partition) {
        foreach (mp_info_pages[i][1][k]) {
          mp_info_pages[i][1][k].program_en == MuBi4False;
          mp_info_pages[i][1][k].erase_en == MuBi4False;
        }
      }
    }

    foreach (mp_info_pages[i, j]) {
      mp_info_pages[i][j].size() == flash_ctrl_pkg::InfoTypeSize[j];

      foreach (mp_info_pages[i][j][k]) {
       mp_info_pages[i][j][k].en dist {
                               MuBi4True := 4,
                               MuBi4False := 1
                               };

        mp_info_pages[i][j][k].scramble_en == MuBi4False;

        mp_info_pages[i][j][k].ecc_en == MuBi4False;

        mp_info_pages[i][j][k].he_en dist {
          MuBi4False :/ (100 - cfg.seq_cfg.mp_info_page_he_en_pc[i][j]),
          MuBi4True  :/ cfg.seq_cfg.mp_info_page_he_en_pc[i][j]
        };
      }
    }
  }

  // Default flash ctrl region settings.
  rand mubi4_t default_region_read_en;
  rand mubi4_t default_region_program_en;
  rand mubi4_t default_region_erase_en;
  rand mubi4_t default_region_he_en;
  mubi4_t default_region_scramble_en;
  mubi4_t default_region_ecc_en;

  // Bank erasability.
  rand bit [flash_ctrl_pkg::NumBanks-1:0] bank_erase_en;

  constraint default_region_he_en_c {
    default_region_he_en dist {
      MuBi4True  :/ cfg.seq_cfg.default_region_he_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_he_en_pc)
    };
  }

  rand data_q_t flash_op_data;
  uvm_reg_data_t data;
  // number of randomized transactions
  int num_trans = 100;
  int iter = 0;

  virtual task pre_start();
    super.pre_start();
    // Flash operations can create multiple recov_err alerts.
    // With default ack_*_max values, sometimes, alert agent missed catching
    // every recov_err. So reduce max value to get finer detect resolution.
    cfg.m_alert_agent_cfgs["recov_err"].ack_delay_max = 5;
    cfg.m_alert_agent_cfgs["recov_err"].ack_stable_max = 5;
  endtask // pre_start

  virtual task body();
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::On;
    cfg.scb_check                               = 1;

    repeat (num_trans) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      cfg.default_region_cfg.read_en = default_region_read_en;
      cfg.default_region_cfg.program_en = default_region_program_en;
      cfg.default_region_cfg.erase_en = default_region_erase_en;
      cfg.default_region_cfg.he_en = default_region_he_en;
      init_p2r_map();
      update_p2r_map(mp_regions);

      do_mp_reg();
      if (illegal_trans) begin
        exp_alert_cnt++;
      end
      illegal_trans = 0;

      // This 'wait' will be terminated by expected_alert's max_delay from scoreboard
      `uvm_info("seq", $sformatf("wait for recov_err alert  exp:%0d   obs:%0d max_delay:%0d",
                                 exp_alert_cnt, cfg.scb_h.alert_count["recov_err"],
                                 cfg.scb_h.expected_alert["recov_err"].max_delay), UVM_MEDIUM)

      `DV_SPINWAIT(wait(cfg.scb_h.alert_count["recov_err"] == exp_alert_cnt);,
                   $sformatf({"wait timeout for alert_count == exp_alertcnt after do_mp_reg() ",
                              "alert_cnt:%0d  exp_alert_cnt:%0d"},
                             cfg.scb_h.alert_count["recov_err"], exp_alert_cnt),
                   cfg.alert_max_delay_in_ns)

      cfg.scb_h.expected_alert["recov_err"].expected = 0;
    end
    // Send info region access and bank erase
    exp_alert_cnt = 0;
    cfg.scb_h.alert_count["recov_err"] = 0;

    `DV_CHECK_RANDOMIZE_FATAL(this)

    configure_flash_protection();
    `uvm_info("seq", $sformatf("info / bank op start... "), UVM_MEDIUM)
    repeat(50) begin
      `uvm_info("seq", $sformatf("iter : %0d", iter++), UVM_MEDIUM)
      //clean scb mem
      cfg.reset_scb_mem();

      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(flash_op,
                                            flash_op.partition == FlashPartInfo;)
      `uvm_info(`gfn, $sformatf("BANK ERASE PART %0p", flash_op), UVM_LOW)
      do_info_bank();
      illegal_trans = 0;
      `uvm_info("do_info_bank", $sformatf("done: alert_cnt  exp:%0d  obs:%0d",
                                exp_alert_cnt, cfg.scb_h.alert_count["recov_err"]),
                                UVM_MEDIUM)

      `DV_SPINWAIT(wait(cfg.scb_h.alert_count["recov_err"] == exp_alert_cnt);,
                   $sformatf({"wait timeout for alert_count == exp_alertcnt after do_info_bank() ",
                              "alert_cnt:%0d  exp_alert_cnt:%0d"},
                             cfg.scb_h.alert_count["recov_err"], exp_alert_cnt),
                   cfg.alert_max_delay_in_ns)

      `DV_SPINWAIT(wait(cfg.scb_h.hs_state == AlertAckComplete);,
                   "wait timeout for hs_state == AlertAckComplete",
                   cfg.alert_max_delay_in_ns)

      cfg.scb_h.expected_alert["recov_err"].expected = 0;
     end
  endtask : body

  virtual task do_mp_reg();
    int page ,bank;
    flash_mp_region_cfg_t my_region;
    poll_fifo_status           = 1;
    // Default region settings
    default_region_ecc_en      = MuBi4False;
    default_region_scramble_en = MuBi4False;
    cfg.allow_spec_info_acc = 3'b111;
    configure_flash_protection();
    // Randomize Write Data
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(flash_op_data,
                                          flash_op_data.size == flash_op.num_words;)
    `uvm_info("do_mp_reg", $sformatf("flash_op: %p", flash_op), UVM_MEDIUM)
    bank = flash_op.addr[OTFBankId];
    // For ctrl read, you have to validate per Qword
    if (flash_op.op == FlashOpRead) begin
      int is_odd = flash_op.addr[2];
      int size = (flash_op.num_words + is_odd) / 2;
      int tail = (flash_op.num_words + is_odd) % 2;
      addr_t tmp_addr = flash_op.addr;
      flash_op.addr[2:0] = 0;

      `uvm_info("do_mp_reg", $sformatf("size:%0d tail:%0d bank:%0d addr:%x",
                                  size, tail, bank, tmp_addr), UVM_MEDIUM)
      for (int i = 0; i < size; i++) begin
        flash_op.otf_addr = flash_op.addr[OTFBankId-1:0];
        if  (flash_op.partition == FlashPartData) begin
          page = cfg.addr2page(flash_op.addr);
          my_region = get_region_from_page(page);
        end else begin
          page = cfg.addr2page(flash_op.addr[OTFBankId-1:0]);
          my_region = cfg.get_region_from_info(mp_info_pages[bank][flash_op.partition>>1][page]);
          illegal_trans |= check_info_part(flash_op, "read_flash");
        end
        illegal_trans |= validate_flash_op(flash_op, my_region);
        flash_op.addr += 8;
      end // for (int i = 0; i < size; i++)
      if (tail) begin
        if  (flash_op.partition == FlashPartData) begin
          page = cfg.addr2page(flash_op.addr);
          my_region = get_region_from_page(page);
        end else begin
          page = cfg.addr2page(flash_op.otf_addr);
          my_region = cfg.get_region_from_info(mp_info_pages[bank][flash_op.partition>>1][page]);
          illegal_trans |= check_info_part(flash_op, "read_flash");
        end
        illegal_trans |= validate_flash_op(flash_op, my_region);
      end // if (tail)
      flash_op.addr = tmp_addr;
    end else begin // if (flash_op.op == FlashOpRead)
      if  (flash_op.partition == FlashPartData) begin
        page = cfg.addr2page(flash_op.addr);
        my_region = get_region_from_page(page);
      end else begin
        page = cfg.addr2page(flash_op.addr[OTFBankId-1:0]);
        my_region = cfg.get_region_from_info(mp_info_pages[bank][flash_op.partition>>1][page]);
      end
      illegal_trans = validate_flash_op(flash_op, my_region);
    end

    if(illegal_trans) begin
      set_otf_exp_alert("recov_err");
    end

    `uvm_info("do_mp_reg", $sformatf("trans:%0d page:%x region:%0d illegal_trans:%0d",
                                     ++trans_cnt, page, cfg.p2r_map[page], illegal_trans),
                                     UVM_MEDIUM)

    if (flash_op.op == FlashOpProgram) begin
      //prepare for program op
      cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));
      flash_ctrl_start_op(flash_op);
      flash_ctrl_write(flash_op_data, poll_fifo_status);
      wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
    end else if (flash_op.op == FlashOpRead) begin
      flash_ctrl_start_op(flash_op);
      flash_ctrl_read(flash_op.num_words, flash_op_data, poll_fifo_status);
      wait_flash_op_done();
    end else begin
      flash_op.addr[10:0] = 'h0;
      flash_ctrl_start_op(flash_op);
      wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
    end
  endtask : do_mp_reg

  virtual task do_info_bank();
    int info_page_addr, num_info_pages;
    int info_sel, bank;

    flash_bank_mp_info_page_cfg_t my_info;

    poll_fifo_status           = 1;

    flash_op.erase_type = flash_ctrl_pkg::FlashEraseBank;
    flash_op.num_words  = 16;
    info_sel = flash_op.partition >> 1;
    bank = flash_op.addr[19];
    num_info_pages = InfoTypeSize[info_sel];
    info_page_addr = $urandom_range(1, num_info_pages) - 1;
    flash_op.addr[18:0] = 'h0;
    flash_op.addr += (BytesPerPage * info_page_addr);
    my_info = mp_info_pages[flash_op.addr[19]][info_sel][info_page_addr];

    // Bank erase
    if (flash_op.op == FlashOpErase) begin
      illegal_trans = (bank_erase_en[bank] == 0);
    end else begin
      illegal_trans = validate_flash_info(flash_op, my_info);
    end

    if(illegal_trans) begin
      if (flash_op.op != FlashOpErase) begin
        cfg.scb_h.expected_alert["recov_err"].expected = 1;
        cfg.scb_h.exp_alert_contd["recov_err"] = 31;
        exp_alert_cnt += 32;
      end else begin
        cfg.scb_h.expected_alert["recov_err"].expected = 1;
        exp_alert_cnt +=1;
      end
      cfg.scb_h.expected_alert["recov_err"].max_delay = 2000; // cycles
    end
    `uvm_info("do_info_bank", $sformatf("flash_op: %p", flash_op), UVM_MEDIUM)
    `uvm_info("do_info_bank", $sformatf("INFO_TBL[%0d][%0d][%0d] = %p", flash_op.addr[19],
                                         info_sel, info_page_addr, my_info), UVM_MEDIUM)
    `uvm_info("do_info_bank", $sformatf("trans:%0d  illegal_trans:%0d exp_alert:%0d op:%s",
                                        ++trans_cnt, illegal_trans,
                                        cfg.scb_h.expected_alert["recov_err"].expected,
                                        flash_op.op.name),
                                        UVM_MEDIUM)

    if (flash_op.op == FlashOpProgram) begin
      controller_program_page(flash_op);
    end else if (flash_op.op == FlashOpRead) begin // if (flash_op.op == FlashOpProgram)
      controller_read_page(flash_op);
    end else begin // if (flash_op.op == FlashOpRead)
      `uvm_info("do_info_bank", $sformatf("bank_erase_en[%0d]=%0d",
                                          bank,bank_erase_en[bank]), UVM_MEDIUM)
      flash_ctrl_start_op(flash_op);
      wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
    end
  endtask : do_info_bank

  task configure_flash_protection();
    // Configure the flash with scramble disable.
    foreach (mp_regions[k]) begin
      mp_regions[k].scramble_en = MuBi4False;
      flash_ctrl_mp_region_cfg(k, mp_regions[k]);
      `uvm_info(`gfn, $sformatf("MP regions values %p", mp_regions[k]), UVM_HIGH)
    end

    flash_ctrl_default_region_cfg(
        .read_en(default_region_read_en), .program_en(default_region_program_en),
        .erase_en(default_region_erase_en), .scramble_en(default_region_scramble_en),
        .ecc_en(default_region_ecc_en), .he_en(default_region_he_en));

    foreach (mp_info_pages[i, j, k]) begin
      flash_ctrl_mp_info_page_cfg(i, j, k, mp_info_pages[i][j][k]);
    end
    //Enable Bank erase
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));
  endtask // configure_flash_protection

  function flash_mp_region_cfg_t get_region_from_page(int page, bit dis = 1);
    flash_mp_region_cfg_t my_region;
    if (cfg.p2r_map[page] == 8) begin
      my_region = cfg.default_region_cfg;
    end else begin
      my_region = this.mp_regions[cfg.p2r_map[page]];
      if (my_region.en != MuBi4True) my_region = cfg.default_region_cfg;
    end
    if (dis) begin
      `uvm_info("get_region_from_page", $sformatf("page:%0d --> region:%0d",
                                        page, cfg.p2r_map[page]), UVM_MEDIUM)
    end
    return my_region;
  endfunction // get_region_from_page

endclass : flash_ctrl_mp_regions_vseq
