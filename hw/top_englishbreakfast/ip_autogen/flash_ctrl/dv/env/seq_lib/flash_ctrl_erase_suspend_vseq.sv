// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Erase suspend test. Activate Erase suspend in following cases:
// 1. Scenario - Erase is not active
// 2. Scenario - Erase is in progress
class flash_ctrl_erase_suspend_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_erase_suspend_vseq)

  `uvm_object_new

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();
    // number of transactions
    cfg.seq_cfg.max_num_trans                 = 15;

    // no overlap mp regions
    cfg.seq_cfg.allow_mp_region_overlap       = 0;

    // enable scramble
    cfg.seq_cfg.mp_region_scramble_en_pc      = 50;
    cfg.seq_cfg.default_region_scramble_en_pc = 50;

    // enable high endurance
    cfg.seq_cfg.mp_region_he_en_pc            = 50;
    cfg.seq_cfg.default_region_he_en_pc       = 50;

    // randomize memory
    cfg.seq_cfg.flash_init_set_pc             = 0;
  endfunction

  // Flash ctrl operation data queue - used for programing or reading the flash.
  data_q_t    flash_op_data;

  // Randomized flash ctrl operation.
  rand flash_op_t flash_op;

  // Constraint address to be in relevant range for the selected partition.
  constraint addr_c {
    if (flash_op.partition != FlashPartData) {
      flash_op.addr inside
       {[0:InfoTypeBytes[flash_op.partition>>1]-1],
        [BytesPerBank:BytesPerBank+InfoTypeBytes[flash_op.partition>>1]-1]};
    }
  }

  constraint flash_op_c {
    flash_op.addr inside {[0 : FlashSizeBytes - 1]};
    flash_op.op == flash_ctrl_pkg::FlashOpErase;

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

  // Bit vector representing which of the mp region cfg CSRs to enable.
  rand bit [flash_ctrl_pkg::MpRegions-1:0] en_mp_regions;

  constraint en_mp_regions_c {$countones(en_mp_regions) == cfg.seq_cfg.num_en_mp_regions;}

  // Memory protection regions settings.
  rand flash_mp_region_cfg_t mp_regions[flash_ctrl_pkg::MpRegions];

  constraint mp_regions_c {
    solve en_mp_regions before mp_regions;

    foreach (mp_regions[i]) {
      mp_regions[i].en == mubi4_bool_to_mubi(en_mp_regions[i]);

      mp_regions[i].read_en == MuBi4True;

      mp_regions[i].program_en == MuBi4True;

      mp_regions[i].erase_en == MuBi4True;

      mp_regions[i].scramble_en == MuBi4False;

      mp_regions[i].ecc_en == MuBi4False;

      mp_regions[i].he_en dist {
        MuBi4False :/ (100 - cfg.seq_cfg.mp_region_he_en_pc),
        MuBi4True  :/ cfg.seq_cfg.mp_region_he_en_pc
      };

      mp_regions[i].start_page inside {[0 : FlashNumPages - 1]};
      mp_regions[i].num_pages inside {[1 : FlashNumPages - mp_regions[i].start_page]};
      mp_regions[i].num_pages <= cfg.seq_cfg.mp_region_max_pages;

      // If overlap not allowed, then each configured region is uniquified.
      // This creates an ascending order of mp_regions that are configured, so we shuffle it in
      // post_randomize.
      if (!cfg.seq_cfg.allow_mp_region_overlap) {
        foreach (mp_regions[j]) {
          if (i != j) {
            !mp_regions[i].start_page inside {
              [mp_regions[j].start_page:mp_regions[j].start_page + mp_regions[j].num_pages]
            };
          }
        }
      }
    }
  }

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

        mp_info_pages[i][j][k].ecc_en == MuBi4False;

        mp_info_pages[i][j][k].he_en dist {
          MuBi4False :/ (100 - cfg.seq_cfg.mp_info_page_he_en_pc[i][j]),
          MuBi4True  :/ cfg.seq_cfg.mp_info_page_he_en_pc[i][j]
        };
      }
    }
  }

  // Default flash ctrl region settings.
  mubi4_t default_region_read_en;
  mubi4_t default_region_program_en;
  mubi4_t default_region_erase_en;
  rand mubi4_t default_region_scramble_en;
  rand mubi4_t default_region_he_en;
  mubi4_t default_region_ecc_en;

  constraint default_scramble_he_en_c {
    default_region_scramble_en dist {
      MuBi4True  :/ cfg.seq_cfg.default_region_scramble_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_scramble_en_pc)
    };
  }

  constraint default_region_he_en_c {
    default_region_he_en dist {
      MuBi4True  :/ cfg.seq_cfg.default_region_he_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_he_en_pc)
    };
  }

  // Bank erasability.
  rand bit [flash_ctrl_pkg::NumBanks-1:0] bank_erase_en;

  constraint bank_erase_en_c {
    foreach (bank_erase_en[i]) {
      bank_erase_en[i] == 1;
    }
  }

  data_q_t flash_rd_data;
  uvm_reg_data_t data;

  virtual task body();
    repeat (cfg.seq_cfg.max_num_trans) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      reset_flash();
      do_erase();
      // Check that the erase suspended by initiating a read to another page of the flash and make
      // sure it completes in a reasonable time relevant for read - cfg.seq_cfg.read_timeout_ns.
      check_erase_suspended();
      // Check recovery by initiating an additional erase to the affected page and backdoor
      // verify it.
      // After an erase is suspended, the page must be erased before any other transaction can be
      // initiated to the selected page.
      check_recovery();
    end
  endtask : body

  virtual task do_erase();
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::On;
    // Default region settings
    default_region_read_en    = MuBi4True;
    default_region_program_en = MuBi4True;
    default_region_erase_en   = MuBi4True;
    default_region_ecc_en     = MuBi4False;

    // Configure the flash with scramble disable.
    foreach (mp_regions[k]) begin
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

    // 1. Scenario - erase is not active
    `uvm_info(`gfn, $sformatf("Scenario 1: Erase is not active"), UVM_HIGH)

    // Read data before writing
    csr_rd(.ptr(ral.erase_suspend), .value(data));
    `uvm_info(`gfn, $sformatf("ERASE SUSPEND DATA BEFORE WR: %0p", data), UVM_HIGH)

    // Invoke erase suspend request
    csr_wr(.ptr(ral.erase_suspend), .value(1));
    `uvm_info(`gfn, $sformatf("ERASE SUSPEND DATA AFTER WR: %0p", data), UVM_HIGH)

    // value of error suspend request should be imediatelly cleared when
    // erase is not in progress
    csr_rd_check(.ptr(ral.erase_suspend.req), .compare_value(0));

    // 2. Scneario - Erase is in progress
    `uvm_info(`gfn, $sformatf("Scenario 2: Erase is in progress"), UVM_HIGH)

    `uvm_info(`gfn, $sformatf("FLASH OP ERASE START OP: %0p", flash_op), UVM_HIGH)
    flash_ctrl_start_op(flash_op);

    `uvm_info(`gfn, $sformatf("START COUNTING BEFORE ES REQ"), UVM_HIGH)
    cfg.clk_rst_vif.wait_clks($urandom_range(50, 100));
    csr_wr(.ptr(ral.erase_suspend), .value(1));
    `uvm_info(`gfn, $sformatf("ERASE SUSPEND REQUESTED"), UVM_HIGH)

    // WAITING THAT ERASE SUSPEND REQ IS DONE AND REQ RETURNED TO ZERO
    `DV_SPINWAIT(do begin
                   csr_rd(.ptr(ral.erase_suspend), .value(data));
                   `uvm_info(`gfn, $sformatf("ERASE SUSPEND REQ: %0p", data), UVM_HIGH)
                 end while (data == 1);,
                 "ERASE SUSPEND TIMEOUT OCCURED!", cfg.seq_cfg.erase_timeout_ns)

    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_suspend_expected_time_ns));

  endtask : do_erase

  // Check that the erase suspended by initiating a read to another page of the flash and make
  // sure it completes in a reasonable time relevant for read - cfg.seq_cfg.read_timeout_ns.
  // If the erase that suspended was bank-erase, make sure to read from the other bank.
  task check_erase_suspended();
    flash_op_t flash_op_erase = flash_op;
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(flash_op,
                     flash_op.partition != flash_op_erase.partition ||
                     flash_op.addr[FlashMemAddrBankMsbBit-:(FlashBankWidth+FlashPageWidth)] !=
                     flash_op_erase.addr[FlashMemAddrBankMsbBit-:(FlashBankWidth+FlashPageWidth)];
                     if (flash_op_erase.erase_type == flash_ctrl_pkg::FlashEraseBank) {
                       flash_op.addr[FlashMemAddrBankMsbBit] !=
                       flash_op_erase.addr[FlashMemAddrBankMsbBit];
                     })
    flash_op.op = FlashOpRead;
    `uvm_info(`gfn, $sformatf("START READ DIFFERENT PAGE TO CHECK THE ERASE IS SUSPENDED, op: %p",
                              flash_op), UVM_HIGH)
    flash_ctrl_start_op(flash_op);
    flash_ctrl_read(flash_op.num_words, flash_op_data, 1'b0);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.read_timeout_ns));
    flash_op = flash_op_erase;
  endtask : check_erase_suspended

  // Task to run another erase on the page in which the erase-suspend done and check it complete
  // successfully.
  // After an erase is suspended, the page must be erased before any other transaction can be
  // initiated to the selected page.
  task check_recovery();
    // Expected data.
    data_q_t    exp_data;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flash_op_data, flash_op_data.size() == 0;)

    `uvm_info(`gfn, $sformatf("START ERASE THE SAME PAGE TO CHECK RECOVERY flash_ctrl op: %p",
                              flash_op), UVM_HIGH)
    flash_ctrl_start_op(flash_op);
    exp_data = cfg.calculate_expected_data(flash_op, flash_op_data);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
    cfg.flash_mem_bkdr_erase_check(flash_op, exp_data);

  endtask : check_recovery

endclass : flash_ctrl_erase_suspend_vseq
