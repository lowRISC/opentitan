// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Full memory access test. First flash is first programmed and than read back
// by controller. Second direct reads are invoked.
class flash_ctrl_full_mem_access_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_full_mem_access_vseq)

  `uvm_object_new

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();

    // enable high endurance
    cfg.seq_cfg.mp_region_he_en_pc      = 50;
    cfg.seq_cfg.default_region_he_en_pc = 50;

  endfunction

  rand flash_op_t flash_op;
  rand bit        selected_bank;
  addr_t bank_start_addr;

  // Memory protection regions settings.
  flash_mp_region_cfg_t mp_regions[flash_ctrl_pkg::MpRegions];

  // Information partitions memory protection pages settings.
  rand flash_bank_mp_info_page_cfg_t
             mp_info_pages[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes][$];

  constraint mp_info_pages_c {
    foreach (mp_info_pages[i, j]) {
      mp_info_pages[i][j].size() == flash_ctrl_pkg::InfoTypeSize[j];
      foreach (mp_info_pages[i][j][k]) {
        mp_info_pages[i][j][k].en == MuBi4True;
        mp_info_pages[i][j][k].read_en == MuBi4True;
        mp_info_pages[i][j][k].program_en == MuBi4True;
        mp_info_pages[i][j][k].erase_en == MuBi4True;
        mp_info_pages[i][j][k].scramble_en == MuBi4False;
        mp_info_pages[i][j][k].ecc_en == MuBi4False;
        mp_info_pages[i][j][k].he_en dist {
          MuBi4False :/ (100 - cfg.seq_cfg.mp_region_he_en_pc),
          MuBi4True :/ cfg.seq_cfg.mp_region_he_en_pc
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
      MuBi4True :/ cfg.seq_cfg.default_region_he_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_he_en_pc)
    };
  }

  virtual task body();
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::On;
    cfg.scb_check                               = 1;

    `DV_CHECK_RANDOMIZE_FATAL(this)
    bank_start_addr = selected_bank * BytesPerBank;
    `uvm_info(`gfn, $sformatf("SW PROGRAM AND READ DATA FROM BANK %0d", selected_bank), UVM_LOW)
    do_sw_rw();
    `uvm_info(`gfn, $sformatf("DIRECT READ DATA FROM BANK %0d", selected_bank), UVM_LOW)
    do_direct_rd();

  endtask : body

  virtual task do_sw_rw();
    flash_op_t flash_op_sw_rw;
    // Default region settings
    default_region_read_en     = MuBi4True;
    default_region_program_en  = MuBi4True;
    default_region_erase_en    = MuBi4True;
    default_region_ecc_en      = MuBi4False;
    default_region_scramble_en = MuBi4False;
    flash_ctrl_default_region_cfg(
        .read_en(default_region_read_en), .program_en(default_region_program_en),
        .erase_en(default_region_erase_en), .scramble_en(default_region_scramble_en),
        .ecc_en(default_region_ecc_en), .he_en(default_region_he_en));

    // No Protection
    foreach (mp_regions[i]) begin
      mp_regions[i].en = MuBi4False;
    end
    foreach (mp_regions[k]) begin
      flash_ctrl_mp_region_cfg(k, mp_regions[k]);
      `uvm_info(`gfn, $sformatf("MP regions values %p", mp_regions[k]), UVM_HIGH)
    end

    foreach (mp_info_pages[i, j, k]) begin
      flash_ctrl_mp_info_page_cfg(i, j, k, mp_info_pages[i][j][k]);
      `uvm_info(`gfn, $sformatf("MP INFO regions values %p", mp_info_pages[i][j][k]), UVM_HIGH)
    end
    //Enable Bank erase
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));

    flash_op_sw_rw.partition  = FlashPartData;
    flash_op_sw_rw.erase_type = flash_ctrl_pkg::FlashEraseBank;
    flash_op_sw_rw.op         = flash_ctrl_pkg::FlashOpProgram;
    flash_op_sw_rw.num_words  = 16;
    flash_op_sw_rw.addr       = bank_start_addr;

    `uvm_info(`gfn, $sformatf("PROGRAM DATA PART %p", flash_op_sw_rw), UVM_LOW)
    for (int i = 0; i < NUM_PAGE_PART_DATA; i++) begin
      controller_program_page(flash_op_sw_rw);
      flash_op_sw_rw.addr = flash_op_sw_rw.addr + BytesPerPage;
    end

    flash_op_sw_rw.partition = FlashPartInfo;
    flash_op_sw_rw.addr = bank_start_addr;
    `uvm_info(`gfn, $sformatf("PROGRAM INFO PART %p", flash_op_sw_rw), UVM_LOW)
    for (int i = 0; i < NUM_PAGE_PART_INFO0; i++) begin
      controller_program_page(flash_op_sw_rw);
      flash_op_sw_rw.addr = flash_op_sw_rw.addr + BytesPerPage;
    end

    flash_op_sw_rw.partition = FlashPartInfo1;
    flash_op_sw_rw.addr = bank_start_addr;
    `uvm_info(`gfn, $sformatf("PROGRAM INFO1 PART %p", flash_op_sw_rw), UVM_LOW)
    for (int i = 0; i < NUM_PAGE_PART_INFO1; i++) begin
      controller_program_page(flash_op_sw_rw);
      flash_op_sw_rw.addr = flash_op_sw_rw.addr + BytesPerPage;
    end

    flash_op_sw_rw.partition = FlashPartInfo2;
    flash_op_sw_rw.addr = bank_start_addr;
    `uvm_info(`gfn, $sformatf("PROGRAM INFO2 PART %p", flash_op_sw_rw), UVM_LOW)
    for (int i = 0; i < NUM_PAGE_PART_INFO2; i++) begin
      controller_program_page(flash_op_sw_rw);
      flash_op_sw_rw.addr = flash_op_sw_rw.addr + BytesPerPage;
    end

    flash_op_sw_rw.partition = FlashPartData;
    flash_op_sw_rw.addr = bank_start_addr;
    `uvm_info(`gfn, $sformatf("READ DATA PART %p", flash_op_sw_rw), UVM_LOW)
    for (int i = 0; i < NUM_PAGE_PART_DATA; i++) begin
      controller_read_page(flash_op_sw_rw);
      flash_op_sw_rw.addr = flash_op_sw_rw.addr + BytesPerPage;
    end

    flash_op_sw_rw.partition = FlashPartInfo;
    flash_op_sw_rw.addr = bank_start_addr;
    `uvm_info(`gfn, $sformatf("READ INFO PART %p", flash_op_sw_rw), UVM_LOW)
    for (int i = 0; i < NUM_PAGE_PART_INFO0; i++) begin
      controller_read_page(flash_op_sw_rw);
      flash_op_sw_rw.addr = flash_op_sw_rw.addr + BytesPerPage;
    end

    flash_op_sw_rw.partition = FlashPartInfo1;
    flash_op_sw_rw.addr = bank_start_addr;
    `uvm_info(`gfn, $sformatf("READ INFO1 PART %p", flash_op_sw_rw), UVM_LOW)
    for (int i = 0; i < NUM_PAGE_PART_INFO1; i++) begin
      controller_read_page(flash_op_sw_rw);
      flash_op_sw_rw.addr = flash_op_sw_rw.addr + BytesPerPage;
    end

    flash_op_sw_rw.partition = FlashPartInfo2;
    flash_op_sw_rw.addr = bank_start_addr;
    `uvm_info(`gfn, $sformatf("READ INFO2 PART %p", flash_op_sw_rw), UVM_LOW)
    for (int i = 0; i < NUM_PAGE_PART_INFO2; i++) begin
      controller_read_page(flash_op_sw_rw);
      flash_op_sw_rw.addr = flash_op_sw_rw.addr + BytesPerPage;
    end
  endtask : do_sw_rw

  virtual task do_direct_rd();
    bit   [TL_AW-1:0] read_addr;
    bit   [TL_AW-1:0] start_addr;
    data_4s_t rdata;
    bit               comp;
    start_addr = bank_start_addr;
    cfg.dir_rd_in_progress = 1'b1;
    for (int i = 0; i < NUM_BK_DATA_WORDS; i++) begin
      read_addr = start_addr + 4 * i;
      `uvm_info(`gfn, $sformatf("Direct read address 0x%0h", read_addr), UVM_HIGH)
      do_direct_read(.addr(read_addr), .mask('1), .blocking(1), .check_rdata(0), .rdata(rdata),
                     .completed(comp));
    end
    csr_utils_pkg::wait_no_outstanding_access();
    cfg.dir_rd_in_progress = 1'b0;
  endtask : do_direct_rd

endclass : flash_ctrl_full_mem_access_vseq
