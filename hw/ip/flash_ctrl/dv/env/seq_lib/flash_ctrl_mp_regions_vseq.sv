// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Memory protect test. Overlapping regions with randomization.
// Flash is first programmed and than read back.
class flash_ctrl_mp_regions_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_mp_regions_vseq)

  `uvm_object_new

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();

    // set page erase as default
    cfg.seq_cfg.op_erase_type_bank_pc   = 0;

    // enable high endurance
    cfg.seq_cfg.mp_region_he_en_pc      = 50;
    cfg.seq_cfg.default_region_he_en_pc = 50;

    // info1 partition is not read only
    cfg.seq_cfg.op_readonly_on_info1_partition = 0;
  endfunction

  rand flash_op_t flash_op;
  flash_op_t      flash_op_pg_erase;
  flash_op_t      flash_op_bk_erase;

  localparam bit [TL_DW-1:0] ALL_ONES = {TL_DW{1'b1}};

  bit poll_fifo_status;

  // Constraint address to be in relevant range for the selected partition.
  constraint addr_c {
    if (flash_op.partition != FlashPartData) {
      flash_op.addr inside
       {[0:InfoTypeBytes[flash_op.partition>>1]-1],
        [BytesPerBank:BytesPerBank+InfoTypeBytes[flash_op.partition>>1]-1]};
    }
  }

  constraint flash_op_c {
    flash_op.op inside {FlashOpRead, FlashOpProgram,FlashOpErase};
    flash_op.addr inside {[0 : FlashSizeBytes - 1]};
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

  // Memory protection regions settings.
  rand flash_mp_region_cfg_t mp_regions[flash_ctrl_pkg::MpRegions];

  rand flash_mp_region_cfg_t mp_regions_bank[flash_ctrl_pkg::MpRegions];

  constraint mp_regions_c {

    foreach (mp_regions[i]) {

      mp_regions[i].scramble_en == 0;

      mp_regions[i].ecc_en == 0;

      mp_regions[i].he_en dist {
        0 :/ (100 - cfg.seq_cfg.mp_region_he_en_pc),
        1 :/ cfg.seq_cfg.mp_region_he_en_pc
      };

      mp_regions[i].start_page dist {
        0                   :/ 10,
        [1:FlashNumPages-2] :/ 80,
        FlashNumPages-1     :/ 10
      };
      mp_regions[i].num_pages inside {[1 : FlashNumPages - mp_regions[i].start_page]};
      mp_regions[i].num_pages <= cfg.seq_cfg.mp_region_max_pages;
    }
  }

  // Information partitions memory protection pages settings.
  rand flash_bank_mp_info_page_cfg_t
             mp_info_pages[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes][$];

  constraint mp_info_pages_c {

    foreach (mp_info_pages[i]) {
      if (cfg.seq_cfg.op_readonly_on_info_partition) {
        foreach (mp_info_pages[i][0][k]) {
          mp_info_pages[i][0][k].program_en == 0;
          mp_info_pages[i][0][k].erase_en == 0;
        }
      }
      if (cfg.seq_cfg.op_readonly_on_info1_partition) {
        foreach (mp_info_pages[i][1][k]) {
          mp_info_pages[i][1][k].program_en == 0;
          mp_info_pages[i][1][k].erase_en == 0;
        }
      }
    }

    foreach (mp_info_pages[i, j]) {
      mp_info_pages[i][j].size() == flash_ctrl_pkg::InfoTypeSize[j];

      foreach (mp_info_pages[i][j][k]) {

        mp_info_pages[i][j][k].scramble_en == 0;

        mp_info_pages[i][j][k].ecc_en == 0;

        mp_info_pages[i][j][k].he_en dist {
          0 :/ (100 - cfg.seq_cfg.mp_info_page_he_en_pc[i][j]),
          1 :/ cfg.seq_cfg.mp_info_page_he_en_pc[i][j]
        };
      }
    }
  }

  // Default flash ctrl region settings.
  rand bit default_region_read_en;
  rand bit default_region_program_en;
  rand bit default_region_erase_en;
  rand bit default_region_he_en;
  bit default_region_scramble_en;
  bit default_region_ecc_en;

  // Bank erasability.
  rand bit [flash_ctrl_pkg::NumBanks-1:0] bank_erase_en;

  constraint default_region_he_en_c {
    default_region_he_en dist {
      1 :/ cfg.seq_cfg.default_region_he_en_pc,
      0 :/ (100 - cfg.seq_cfg.default_region_he_en_pc)
    };
  }

  rand data_q_t flash_op_data;
  uvm_reg_data_t data;
  // number of randomized transactions
  int num_trans = 100;

  virtual task body();
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::On;
    cfg.scb_check              = 1;
    cfg.scb_set_exp_alert      = 1;
    cfg.alert_max_delay        = 100_000_000;
    cfg.scb_empty_mem          = 0;
    cfg.scb_set_mem            = 0;
    repeat (num_trans) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      do_mp_reg();
    end

    if (cfg.bank_erase_enable) begin
      //clean scb mem
      reset_scb_mem();
      `DV_CHECK_RANDOMIZE_WITH_FATAL(this,
                                    flash_op.partition inside {FlashPartData,FlashPartInfo};)
      `uvm_info(`gfn, $sformatf("BANK ERASE PART %0p", flash_op), UVM_LOW)
      do_bank_erase();
    end
  endtask : body

  virtual task do_mp_reg();
    poll_fifo_status           = 1;
    // Default region settings
    default_region_ecc_en      = 0;
    default_region_scramble_en = 0;

    // Configure the flash with scramble disable.
    foreach (mp_regions[k]) begin
      mp_regions[k].scramble_en = 0;
      flash_ctrl_mp_region_cfg(k, mp_regions[k]);
      `uvm_info(`gfn, $sformatf("MP regions values %p", mp_regions[k]), UVM_HIGH)
    end

    flash_ctrl_default_region_cfg(
        .read_en(default_region_read_en), .program_en(default_region_program_en),
        .erase_en(default_region_erase_en), .scramble_en(default_region_scramble_en),
        .ecc_en(default_region_ecc_en), .he_en(default_region_he_en));

    foreach (mp_info_pages[i, j, k]) begin
      flash_ctrl_mp_info_page_cfg(i, j, k, mp_info_pages[i][j][k]);
      `uvm_info(`gfn, $sformatf("MP INFO regions values %p", mp_info_pages[i][j][k]), UVM_HIGH)
    end
    //Enable Bank erase
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));

    // Randomize Write Data
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(flash_op_data, flash_op_data.size == flash_op.num_words;)

    if (flash_op.op != flash_ctrl_pkg::FlashOpErase) begin
      //prepare for program op
      cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));
      cfg.scb_set_mem    = 1;
      set_scb_mem(flash_op.num_words,flash_op.partition,flash_op.addr,ALL_ONES);
      cfg.scb_set_mem    = 0;
      // FLASH Program Operation
      flash_op.op = flash_ctrl_pkg::FlashOpProgram;
      flash_ctrl_start_op(flash_op);
      flash_ctrl_write(flash_op_data, poll_fifo_status);
      wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));

      // FLASH Read Operation of previous programmed data
      flash_op.op = flash_ctrl_pkg::FlashOpRead;
      flash_ctrl_start_op(flash_op);
      flash_ctrl_read(flash_op.num_words, flash_op_data, poll_fifo_status);
      wait_flash_op_done();
    end

    if ((flash_op.op == flash_ctrl_pkg::FlashOpErase) &&
        (flash_op.erase_type == flash_ctrl_pkg::FlashErasePage)) begin
      flash_op_pg_erase.partition  = flash_op.partition;
      flash_op_pg_erase.erase_type = flash_ctrl_pkg::FlashErasePage;
      flash_op_pg_erase.op         = flash_ctrl_pkg::FlashOpProgram;
      flash_op_pg_erase.num_words  = 16;
      flash_op_pg_erase.addr       = {flash_op.addr[19:11], {11{1'b0}}};
      // FLASH Erase Page Operation of previous programmed data
      `uvm_info(`gfn, $sformatf("PROGRAM OP %p", flash_op_pg_erase), UVM_HIGH)
      cfg.scb_set_mem    = 1;
      for (int i = 0; i < 32; i++) begin
        set_scb_mem(flash_op_pg_erase.num_words,flash_op_pg_erase.partition,
                    flash_op_pg_erase.addr,ALL_ONES);
        flash_op_pg_erase.addr = flash_op_pg_erase.addr + 64; //64B was written, 16 words
      end
      cfg.scb_set_mem    = 0;
      flash_op_pg_erase.addr       = {flash_op.addr[19:11], {11{1'b0}}};
      controller_program_page(flash_op_pg_erase);
      flash_op_pg_erase.op = flash_ctrl_pkg::FlashOpErase;
      flash_op_pg_erase.addr       = {flash_op.addr[19:11], {11{1'b0}}};
      `uvm_info(`gfn, $sformatf("ERASE OP %p", flash_op_pg_erase), UVM_HIGH)
      flash_ctrl_start_op(flash_op_pg_erase);
      wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
      `uvm_info(`gfn, $sformatf("READ OP %p", flash_op_pg_erase), UVM_HIGH)
      flash_op_pg_erase.addr       = {flash_op.addr[19:11], {11{1'b0}}};
      controller_read_page(flash_op_pg_erase);
    end

  endtask : do_mp_reg

  virtual task do_bank_erase();
    poll_fifo_status           = 1;
    // Default region settings
    default_region_read_en     = 1;
    default_region_program_en  = 1;
    default_region_ecc_en      = 0;
    default_region_scramble_en = 0;

    // No Protection due to sw wr/rd
    foreach (mp_regions[i]) begin
      mp_regions[i].en = 1;
      mp_regions[i].read_en = 1;
      mp_regions[i].program_en = 1;
      mp_regions[i].scramble_en = 0;
      mp_regions[i].ecc_en = 0;
    end

    foreach (mp_info_pages[0][0][k]) begin
      mp_info_pages[0][0][k].en          = 1;
      mp_info_pages[0][0][k].read_en     = 1;
      mp_info_pages[0][0][k].program_en  = 1;
      mp_info_pages[0][0][k].scramble_en = 0;
      mp_info_pages[0][0][k].ecc_en      = 0;
      mp_info_pages[1][0][k].en          = 1;
      mp_info_pages[1][0][k].read_en     = 1;
      mp_info_pages[1][0][k].program_en  = 1;
      mp_info_pages[1][0][k].scramble_en = 0;
      mp_info_pages[1][0][k].ecc_en      = 0;
    end

    // Configure the flash with scramble disable.
    foreach (mp_regions[k]) begin
      mp_regions[k].scramble_en = 0;
      flash_ctrl_mp_region_cfg(k, mp_regions[k]);
      `uvm_info(`gfn, $sformatf("MP regions values %p", mp_regions[k]), UVM_HIGH)
    end

    flash_ctrl_default_region_cfg(
        .read_en(default_region_read_en), .program_en(default_region_program_en),
        .erase_en(default_region_erase_en), .scramble_en(default_region_scramble_en),
        .ecc_en(default_region_ecc_en), .he_en(default_region_he_en));

    foreach (mp_info_pages[i, j, k]) begin
      flash_ctrl_mp_info_page_cfg(i, j, k, mp_info_pages[i][j][k]);
      `uvm_info(`gfn, $sformatf("MP INFO regions values %p", mp_info_pages[i][j][k]), UVM_LOW)
    end

    `uvm_info(`gfn, $sformatf("BANK ERASE values 0x%0h", bank_erase_en), UVM_LOW)
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));

    flash_op_bk_erase.partition  = FlashPartData;
    flash_op_bk_erase.erase_type = flash_ctrl_pkg::FlashEraseBank;
    flash_op_bk_erase.op         = flash_ctrl_pkg::FlashOpProgram;
    flash_op_bk_erase.num_words  = 16;
    flash_op_bk_erase.addr       = {flash_op.addr[19], {19{1'b0}}};

    `uvm_info(`gfn, $sformatf("PROGRAM OP %p", flash_op_bk_erase), UVM_LOW)
    for (int i=0; i < 512; i++ ) begin
      controller_program_page(flash_op_bk_erase);
      flash_op_bk_erase.addr = flash_op_bk_erase.addr + BytesPerPage;
    end

    if (flash_op.partition == FlashPartInfo) begin
      flash_op_bk_erase.partition = FlashPartInfo;
      flash_op_bk_erase.addr = {flash_op.addr[19], {19{1'b0}}};
      `uvm_info(`gfn, $sformatf("PROGRAM OP %p", flash_op_bk_erase), UVM_LOW)
      for (int i=0; i < 10; i++ ) begin
        controller_program_page(flash_op_bk_erase);
        flash_op_bk_erase.addr = flash_op_bk_erase.addr + BytesPerPage;
      end
    end

    flash_op_bk_erase.op = flash_ctrl_pkg::FlashOpErase;
    flash_op_bk_erase.addr = flash_op.addr;
    `uvm_info(`gfn, $sformatf("ERASE OP %p", flash_op_bk_erase), UVM_LOW)
    flash_ctrl_start_op(flash_op_bk_erase);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));

    flash_op_bk_erase.partition = FlashPartData;
    flash_op_bk_erase.addr = {flash_op.addr[19], {19{1'b0}}};
    `uvm_info(`gfn, $sformatf("READ OP %p", flash_op_bk_erase), UVM_LOW)
    for (int i=0; i < 512; i++ ) begin
       controller_read_page(flash_op_bk_erase);
      flash_op_bk_erase.addr = flash_op_bk_erase.addr + BytesPerPage;
    end

    if (flash_op.partition == FlashPartInfo) begin
      flash_op_bk_erase.partition = FlashPartInfo;
      flash_op_bk_erase.addr = {flash_op.addr[19], {19{1'b0}}};
      `uvm_info(`gfn, $sformatf("READ OP %p", flash_op_bk_erase), UVM_LOW)
      for (int i=0; i < 10; i++ ) begin
        controller_read_page(flash_op_bk_erase);
        flash_op_bk_erase.addr = flash_op_bk_erase.addr + BytesPerPage;
      end
    end
  endtask : do_bank_erase

endclass : flash_ctrl_mp_regions_vseq
