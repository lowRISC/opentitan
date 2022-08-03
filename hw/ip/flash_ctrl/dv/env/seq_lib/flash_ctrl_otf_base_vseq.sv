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

  // Number of controller transactions
  // Min: 1 Max:32
  rand int  ctrl_num;
  rand bit  is_addr_odd;
  rand int  fractions;

  // flash op
  // WIP. not all field is valid.
  rand flash_op_t rand_op;

  // Permission to access special partition
  rand bit [2:0] allow_spec_info_acc;

  rand flash_mp_region_cfg_t rand_regions[MpRegions];

  constraint rand_regions_c {
    foreach (rand_regions[i]) {
      rand_regions[i].start_page dist {
        0                       := 1,
        [1 : FlashNumPages - 2] :/ 8,
        FlashNumPages - 1       := 1
      };
      rand_regions[i].num_pages inside {[1 : FlashNumPages - rand_regions[i].start_page]};
      rand_regions[i].num_pages <= 32;
    }
  }

  constraint ctrl_num_c { ctrl_num dist { CTRL_TRANS_MIN := 2, [2:31] :/ 1, CTRL_TRANS_MAX := 2}; }
  constraint fractions_c { fractions dist { [1:4] := 4, [5:16] := 1}; }
  constraint rand_op_c {
    solve flash_program_data before rand_op;
    solve rand_op.partition before rand_op.prog_sel, rand_op.addr;
    solve rand_op.addr before rand_op.otf_addr;

    rand_op.partition dist { FlashPartData := 1, [FlashPartInfo:FlashPartInfo2] :/ 1};
    rand_op.addr[TL_AW-1:BusAddrByteW] == 'h0;
    rand_op.addr[1:0] == 'h0;
    if (rand_op.partition != FlashPartData) {
      rand_op.addr inside {[0:InfoTypeBytes[rand_op.partition>>1]-1]};
      rand_op.prog_sel == 1;
    } else {
      rand_op.prog_sel == 0;
    }
    rand_op.otf_addr == rand_op.addr[BusAddrByteW-2:0];
  }
  constraint special_info_acc_c {
    allow_spec_info_acc dist { 3'h7 := 1, 3'h0 := 1, [1:6] :/ 2};
  }

  virtual task pre_start();
    // Erased page doesn't go through descramble.
    // To maintain high stress rate,
    // keep flash_init to FlashMemInitRandomize
    flash_init_c.constraint_mode(0);
    if (cfg.ecc_mode > FlashEccDisabled) begin
      foreach (cfg.tgt_pre[partition]) begin
        cfg.tgt_pre[partition].shuffle();
        `uvm_info("reset_flash",
                  $sformatf("prefix:%s:rd:%2b dr:%2b wr:%2b",
                            partition.name, cfg.tgt_pre[partition][TgtRd],
                            cfg.tgt_pre[partition][TgtDr], cfg.tgt_pre[partition][TgtWr]),
                  UVM_MEDIUM)
      end
      flash_init = FlashMemInitEccMode;
    end else begin
      flash_init = FlashMemInitRandomize;
    end
    `uvm_info("reset_flash",
              $sformatf("flash_init:%s ecc_mode %0d allow_spec_info_acc:%3b",
                        flash_init.name, cfg.ecc_mode, allow_spec_info_acc), UVM_MEDIUM)

    configure_otf_mode();
    super.pre_start();
    if (cfg.seq_cfg.en_init_keys_seeds == 1) begin
      `DV_SPINWAIT(while (otp_key_init_done != 2'b11) cfg.clk_rst_vif.wait_clks(1);,
                   "timeout waiting  otp_key_init_done", 100_000)
    end

    // Need additional flash update after key init is done
    if (cfg.ecc_mode > FlashEccDisabled) begin
      flash_otf_region_cfg(.scr_en(MuBi4True), .ecc_en(MuBi4True));
      flash_otf_mem_read_zone_init();
      if (cfg.ecc_mode > FlashSerrTestMode) begin
        cfg.scb_h.do_alert_check = 0;
      end
    end else begin
      flash_otf_region_cfg(.scr_en(MuBi4True));
    end
    update_p2r_map(cfg.mp_regions);
    cfg.allow_spec_info_acc = allow_spec_info_acc;
    update_partition_access(cfg.allow_spec_info_acc);
    // Polling init wip is done
    csr_spinwait(.ptr(ral.status.init_wip), .exp_data(1'b0));
    cfg.m_fpp_agent_cfg.mon_start = 1;
  endtask

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
  task prog_flash(ref flash_op_t flash_op, input int bank, int num, int wd = 16);
    data_q_t flash_data_chunk;
    flash_otf_item exp_item;
    bit poll_fifo_status = 1;
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

    if (cfg.ecc_mode > FlashEccDisabled) begin
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

    if (cfg.ecc_mode == FlashEccDisabled) begin
      overflow = end_addr[OTFHostId];
    end else begin
      if (flash_op.partition == FlashPartData) begin
        overflow = (end_addr[18:17] != start_addr[18:17] ||
                    end_addr[16:0] > 17'h1_FE00);
      end else begin
        overflow = (end_addr[10:9] != start_addr[10:9]);
      end
    end

    if (overflow) begin
      if (flash_op.partition == FlashPartData) begin
        start_addr[16:0] = 'h0;
      end else begin
        start_addr[8:0] = 'h0;
      end
      `uvm_info("prog_flash", $sformatf("overflow!, roll over start address to 0x%x",
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
                                          addr2page(flash_op.addr),
                                          flash_op.otf_addr,
                                          end_addr), UVM_MEDIUM)
        is_odd = 0;
      end
      unit_word = wd;
      // Each flash_program_data[] entry : 4B
      // {global_cnt(16bits), lcnt(16bits)}
      for (int j = 0; j < wd; j++) begin
        flash_program_data.push_back({global_pat_cnt, lcnt++});
      end
      flash_op.addr = flash_op.otf_addr;
      // Bank : bit[19]
      flash_op.addr[TL_AW-1:OTFBankId] = bank;
      page = addr2page(flash_op.addr);

      if (flash_op.partition == FlashPartData) begin
        my_region = get_region(page);
        drop = validate_flash_op(flash_op, my_region);
        if (drop) begin
          `uvm_info("prog_flash", $sformatf("op:%s is not allowed in the region:%p",
                                            flash_op.op.name, my_region), UVM_MEDIUM)
          set_otf_exp_alert("recov_err");
        end
      end else begin
        my_region = get_region_from_info(cfg.mp_info[bank][flash_op.partition>>1][page]);
        drop = check_info_part(flash_op, "prog_flash");
      end

      flash_ctrl_start_op(flash_op);
      flash_ctrl_write(flash_program_data, poll_fifo_status);
      wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));

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
      `uvm_info("prog_flash",$sformatf("addr:%x part:%s num:%0d wd:%0d  odd:%0d tail:%0d",
                                       flash_op.otf_addr, flash_op.partition.name, num,
                                       wd, is_odd, tail), UVM_MEDIUM)
      if (drop) begin
        `uvm_info("prog_flash", "skip sb path due to err", UVM_MEDIUM)
      end else begin
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

  // Read flash in the unit of minimum resolution (8 words).
  // 1 word : 8Byte
  // @arg: flash_op_p : command struct return updated address after write
  // @arg: bank: bank index to access flash
  // @arg: num : number of 8 words range: [1 : 32]
  // @arg: wd  : number of 4byte (TL bus unit) : default : 16
  task read_flash(ref flash_op_t flash_op, input int bank, int num, int wd = 16);
    data_q_t flash_read_data;
    flash_otf_item exp_item;
    bit poll_fifo_status = 1;
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

    flash_op.op = FlashOpRead;
    flash_op.num_words = wd;

    if (cfg.ecc_mode == FlashEccDisabled) begin
      flash_op.otf_addr[OTFHostId] = 0;
    end else begin
      if (flash_op.partition == FlashPartData) begin
        flash_op.otf_addr[18:17] = cfg.tgt_pre[flash_op.partition][TgtRd];
      end else begin
        flash_op.otf_addr[10:9] = cfg.tgt_pre[flash_op.partition][TgtRd];
      end
    end
    start_addr = flash_op.otf_addr;
    end_addr = start_addr + (wd * 4 * num) - 1;

    if (cfg.ecc_mode == FlashEccDisabled) begin
      // Ctrl read takes lower half of each bank
      // and host read takes upper half.
      overflow = end_addr[OTFHostId];
    end else begin
      if (flash_op.partition == FlashPartData) begin
        overflow = (end_addr[18:17] != start_addr[18:17] ||
                    end_addr[16:0] > 17'h1_FE00);
      end else begin
        overflow = (end_addr[10:9] != start_addr[10:9]);
      end
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
      if (cfg.ecc_mode > FlashEccDisabled) begin
        if (flash_op.partition == FlashPartData) begin
          flash_op.otf_addr[18:17] = cfg.tgt_pre[flash_op.partition][TgtRd];
        end else begin
          flash_op.otf_addr[10:9] = cfg.tgt_pre[flash_op.partition][TgtRd];
        end
      end
      flash_op.addr = flash_op.otf_addr;
      flash_op.addr[TL_AW-1:OTFBankId] = bank;
      rd_entry.bank = bank;

      `uvm_create_obj(flash_otf_item, exp_item)
      page = addr2page(flash_op.addr);
      `uvm_info("read_flash",
                $sformatf({"bank:%0d page:%0d otf_addr:0x%0h,",
                           " part:%s size:%0d x %0d x 4B start_addr:%x  end_addr:%x"},
                          bank, page, flash_op.otf_addr,
                          flash_op.partition.name, num, wd, start_addr, end_addr),
                UVM_MEDIUM)
      if (flash_op.partition == FlashPartData) begin
        is_odd = flash_op.addr[2];
        size = (flash_op.num_words + is_odd) / 2;
        tail = (flash_op.num_words + is_odd) % 2;
        tmp_addr = flash_op.addr;
        flash_op.addr[2:0] = 0;
        for (int i = 0; i < size; i++) begin
          page = addr2page(flash_op.addr);
          my_region = get_region(page);
          drop |= validate_flash_op(flash_op, my_region);
          flash_op.addr += 8;
        end
        if (tail) begin
          page = addr2page(flash_op.addr);
          my_region = get_region(page);
          drop |= validate_flash_op(flash_op, my_region);
        end
        if (drop) begin
          `uvm_info("read_flash", $sformatf("op:%s is not allowed in the region:%p",
                                            flash_op.op.name, my_region), UVM_MEDIUM)
          set_otf_exp_alert("recov_err");
        end
        flash_op.addr = tmp_addr;
        page = addr2page(flash_op.addr);
        my_region = get_region(page);
      end else begin
        my_region = get_region_from_info(cfg.mp_info[bank][flash_op.partition>>1][page]);
        drop = check_info_part(flash_op, "read_flash");
      end

      exp_item.page = page;
      exp_item.region = my_region;
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
          cfg.scb_h.exp_alert["fatal_err"] = 1;
          cfg.scb_h.alert_chk_max_delay["fatal_err"] = 2000;
          cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

          cfg.scb_h.exp_alert["recov_err"] = 1;
          cfg.scb_h.alert_chk_max_delay["recov_err"] = 2000;
          cfg.scb_h.exp_alert_contd["recov_err"] = 10000;
        end
      end

      `uvm_info("read_flash", $sformatf("read_send %x", flash_op.otf_addr), UVM_HIGH)
      flash_ctrl_start_op(flash_op);
      flash_ctrl_read(flash_op.num_words, flash_read_data, poll_fifo_status);
      wait_flash_op_done();
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
  task otf_direct_read(bit [OTFHostId-2:0] addr, int bank, int num, int dbg = -1);
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

    if (cfg.ecc_mode > FlashEccDisabled) begin
      end_addr = addr + num * 4 - 1;
      overflow = (end_addr[OTFHostId:0] > 18'h1_FE00);
      tl_addr[OTFHostId-:2] = cfg.tgt_pre[FlashPartData][TgtDr];
    end else begin
      end_addr = addr + num * 4 - 1;
      tl_addr[OTFHostId] = 1;
      overflow = end_addr[OTFHostId];
    end

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
      if (cfg.ecc_mode > FlashEccDisabled) tl_addr[18:17] = cfg.tgt_pre[FlashPartData][TgtDr];

      `uvm_create_obj(flash_otf_item, exp_item)
      page = addr2page(tl_addr[OTFBankId-1:0]);
      my_region = get_region(page);
      flash_op.op = FlashOpRead;
      drop = validate_flash_op(flash_op, my_region);
      if (drop) begin
        `uvm_info("direct_read", $sformatf("op:%s is not allowed in the region:%p",
                                           flash_op.op.name, my_region), UVM_MEDIUM)
        set_otf_exp_alert("recov_err");
      end

      exp_item.page = page;
      exp_item.region = my_region;
      exp_item.start_addr = tl_addr;
      exp_item.addr_key = otp_addr_key;
      exp_item.data_key=  otp_data_key;

      rd_entry.addr = tl_addr;
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
      `uvm_info("direct_read", $sformatf("%0d:%0d bank:%0d exec: 0x%x   derr:%0d",
                                          dbg, i, bank, tl_addr, derr), UVM_MEDIUM)
      if (cfg.ecc_mode > FlashSerrTestMode) begin
        if (derr & cfg.scb_h.do_alert_check) begin
          cfg.scb_h.exp_alert["fatal_err"] = 1;
          cfg.scb_h.alert_chk_max_delay["fatal_err"] = 2000;
          cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;
        end
      end
      cfg.inc_otd_tbl(bank, tl_addr, FlashPartData);
      do_direct_read(.addr(tl_addr), .mask('1), .blocking(1), .rdata(rdata),
                     .completed(completed), .exp_err_rsp(derr));
      if (completed) begin
        exp_item.dq.push_back(rdata);
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

  function void update_otf_mem_read_zone(flash_dv_part_e part,
                                         int bank,
                                         addr_t addr);
    flash_otf_item item;
    int page;
    `uvm_create_obj(flash_otf_item, item)
    addr[OTFBankId] = bank;
    page = addr2page(addr);
    item.dq.push_back($urandom());
    item.dq.push_back($urandom());
    item.page = page;
    if (part == FlashPartData) begin
      item.region = get_region(page);
    end else begin
      item.region = get_region_from_info(cfg.mp_info[bank][part>>1][page]);
    end
    // back to per bank addr
    addr[OTFBankId] = 0;
    item.scramble(otp_addr_key, otp_data_key, addr, 0);
    cfg.mem_bkdr_util_h[part][bank].write(addr, item.fq[0]);
  endfunction // update_otf_mem_read_zone

  // Update rd / dr tgt of the memory with their page profile
  function void flash_otf_mem_read_zone_init();
    // 8byte aligned
    addr_t st_addr, ed_addr;

    // read tgt region     : cfg.tgt_pre[0]
    // direct rd tgt region: cfg.tgt_pre[1]
    foreach (cfg.tgt_pre[partition]) begin
      for (int j = TgtRd; j <= TgtDr; j++) begin
        st_addr = 'h0;
        if (partition == FlashPartData) begin
          st_addr[18:17] = cfg.tgt_pre[partition][j];
          // I think this should be
          // 64 * 256 * 8 -1 (= 0x1_FFFF)
          // to maxout a quater of 1 bank
          // Will be address the next PR
          ed_addr = st_addr + 64 * 255 * 8; // + 0x1_FE00
          // data partition 2 banks
          for (int i = 0; i < 2; i++) begin
            for (addr_t addr = st_addr; addr <= ed_addr; addr += 8) begin
              update_otf_mem_read_zone(partition, i, addr);
            end
            `uvm_info("flash_otf_init",
                      $sformatf("partition:%s pre%0d st:%x ed:%x",
                                partition.name, j, st_addr, ed_addr), UVM_MEDIUM)
          end
        end else begin // if (partition == FlashPartData)
          // While data partition can be divided by pages, info partition
          // need finer resolution due to number of pages in each info
          // is relatively small.
          // So every page in info partition will be divided into 4 parts.
          st_addr[10:9] = cfg.tgt_pre[partition][j];
          for (int k = 0; k < InfoTypeSize[partition>>1]; k++) begin
            st_addr[DVPageMSB:DVPageLSB] = k; // page
            ed_addr = st_addr + 511; // 0x1FF
            for (int i = 0; i < 2; i++) begin
              for (addr_t addr = st_addr; addr <= ed_addr; addr += 8) begin
                update_otf_mem_read_zone(partition, i, addr);
              end
            end
            `uvm_info("flash_otf_init",
                      $sformatf("partition:%s pre%0d page:%0d st:%x ed:%x",
                                partition.name, j, k, st_addr, ed_addr), UVM_MEDIUM)
          end
        end

      end
    end
  endfunction // flash_otf_init

  // Send direct host read to both bankds 'host_num' times.
  virtual task send_rand_host_rd(int num = -1, int dbg = -1);
    flash_op_t host;
    int host_num, host_bank;

    host.otf_addr[OTFHostId-2:0] = $urandom();
    host.otf_addr[1:0] = 'h0;
    host.otf_addr[2] = 1;
    if (num >= 0) host_num = num;
    else host_num = $urandom_range(1,128);
    host_bank = $urandom_range(0,1);

    otf_direct_read(host.otf_addr, host_bank, host_num, dbg);
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
    global_derr_is_set = 0;

    cfg.otf_read_entry.hash.delete();
    foreach (cfg.otf_read_entry.prv_read[i]) cfg.otf_read_entry.prv_read[i] = '{};
    cfg.otf_scb_h.clear_fifos();
  endtask // otf_tb_clean_up

  // Populate cfg.mp_info with default_info_page_cfg except scr, ecc.
  // Then program each info region.
  task flash_ctrl_default_info_cfg(mubi4_t scr_en = MuBi4False,
                                   mubi4_t ecc_en = MuBi4False);
    foreach (cfg.mp_info[i, j, k]) begin
           cfg.mp_info[i][j][k] = default_info_page_cfg;
           cfg.mp_info[i][j][k].scramble_en = scr_en;
           cfg.mp_info[i][j][k].ecc_en = ecc_en;
           flash_ctrl_mp_info_page_cfg(i, j, k, cfg.mp_info[i][j][k]);
    end
  endtask // flash_ctrl_info_cfg

  task flash_otf_region_cfg(mubi4_t scr_en = MuBi4False,
                            mubi4_t ecc_en = MuBi4False);

    flash_ctrl_default_region_cfg(,,,scr_en, ecc_en);
    flash_ctrl_default_info_cfg(scr_en, ecc_en);

    foreach (cfg.mp_regions[i]) begin
      cfg.mp_regions[i] = rand_regions[i];
      cfg.mp_regions[i].scramble_en = scr_en;
      cfg.mp_regions[i].ecc_en = ecc_en;
      flash_ctrl_mp_region_cfg(i, cfg.mp_regions[i]);
      `uvm_info("otf_region_cfg", $sformatf("region[%0d] = %p", i, cfg.mp_regions[i]), UVM_MEDIUM)
    end
    `uvm_info("otf_region_cfg", $sformatf("default = %p", default_region_cfg), UVM_MEDIUM)
  endtask

  function flash_mp_region_cfg_t get_region_from_info(flash_bank_mp_info_page_cfg_t info);
    flash_mp_region_cfg_t region;
    region.en          = info.en;
    region.read_en     = info.read_en;
    region.program_en  = info.program_en;
    region.erase_en    = info.erase_en;
    region.scramble_en = info.scramble_en;
    region.ecc_en      = info.ecc_en;
    region.he_en       = info.he_en;
    return region;
  endfunction // get_region_from_info

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

  function void set_otf_exp_alert(string str);
    cfg.scb_h.exp_alert_ff[str].push_back(1);
    cfg.scb_h.alert_chk_max_delay[str] = 2000;
    `uvm_info("set_otf_exp_alert", $sformatf("exp_alert_ff[%s] size: %0d",
                                             str, cfg.scb_h.exp_alert_ff[str].size()), UVM_MEDIUM)
  endfunction // set_otf_exp_alert

  // Check permission and page range of info partition
  // Set exp recov_err alert if check fails
  function bit check_info_part(flash_op_t flash_op, string str);
    bit drop = 0;
    int bank, page, end_page, loop;

    bank = flash_op.addr[OTFBankId];
    page = addr2page(flash_op.addr);
    end_page = addr2page(flash_op.addr + (flash_op.num_words * 4) - 1);
    // For read, cross page boundary is allowed. So you need to check
    // both start and end address
    if (flash_op.op == FlashOpRead) loop = 2;
    else loop = 1;

    for (int i= 0; i < loop; ++i) begin
      if (i == 1) page = end_page;
      if (flash_op.partition == FlashPartInfo && bank == 0 &&
          page inside {[1:3]}) begin
        if (!cfg.allow_spec_info_acc[page-1]) begin
          `uvm_info(str, $sformatf("check_info:page:%0d access is not allowed", page), UVM_MEDIUM)
          set_otf_exp_alert("recov_err");
          drop = 1;
        end
      end
      // check info page range
      if (page >= InfoTypeSize[flash_op.partition>>1]) begin
        `uvm_info(str, $sformatf("check_info:bank:%0d page:%0d addr:0x%0h is out of range",
                                 bank, page, flash_op.otf_addr), UVM_MEDIUM)
        set_otf_exp_alert("recov_err");
        drop = 1;
      end
      if (drop) break;
    end
    return drop;
  endfunction // check_part_info
endclass // flash_ctrl_otf_base_vseq
