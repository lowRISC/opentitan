// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Flash Physical Controller Arbitration between host reads and controller operations
// 1.Scenario tests on the different banks arbitration
// 2.Scenario tests on the same bank arbitration
// 3.Scenario tests lost of priority of host read on the same bank
class flash_ctrl_phy_arb_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_phy_arb_vseq)

  `uvm_object_new

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();
    // MAx number of transactions.
    cfg.seq_cfg.max_num_trans           = 10;

    // Do no more than 16 words per op.
    cfg.seq_cfg.op_max_words            = 16;

    // no overlap mp regions
    cfg.seq_cfg.allow_mp_region_overlap = 0;

    // enable high endurance
    cfg.seq_cfg.mp_region_he_en_pc      = 50;
    cfg.seq_cfg.default_region_he_en_pc = 50;

    cfg.seq_cfg.op_readonly_on_info_partition  = 1;
    cfg.seq_cfg.op_readonly_on_info1_partition = 1;

  endfunction

  // Randomized flash ctrl operation.
  rand flash_op_t flash_op;
  rand flash_op_t flash_op_host_rd;
  data_q_t flash_rd_data;

  rand uint bank;
  rand uint bank_rd;

  // knob for testing arbitration on same or different banks
  logic bank_same = 0;

  bit poll_fifo_status;

  // Constraint for banks.
  constraint bank_c {
    solve bank before bank_rd;
    if (bank_same == 1) {bank == bank_rd;} else {bank != bank_rd;}
    bank inside {[0 : flash_ctrl_pkg::NumBanks - 1]};
    bank_rd inside {[0 : flash_ctrl_pkg::NumBanks - 1]};
  }

  // Constraint controller address to be in relevant range for the selected partition.
  constraint addr_c {
    solve bank before flash_op;
    flash_op.addr inside {[BytesPerBank * bank : BytesPerBank * (bank + 1)]};
    if (flash_op.partition != FlashPartData) {
      flash_op.addr inside
       {[0:InfoTypeBytes[flash_op.partition>>1]-1],
        [BytesPerBank:BytesPerBank+InfoTypeBytes[flash_op.partition>>1]-1]};
    }
  }

  // Constraint host read address to be in relevant range for the selected partition.
  constraint addr_rd_c {
    solve bank_rd before flash_op_host_rd;
    flash_op_host_rd.addr inside {[BytesPerBank * bank_rd :
                                   BytesPerBank * (bank_rd + 1) - BytesPerBank / 2]};
  }

  constraint flash_op_c {
    // Bank erase is supported only for data & 1st info partitions
    flash_op.partition != FlashPartData && flash_op.partition != FlashPartInfo ->
        flash_op.erase_type == flash_ctrl_pkg::FlashErasePage;

    if (cfg.seq_cfg.op_readonly_on_info_partition) {
      flash_op.partition == FlashPartInfo ->
        flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }

    if (cfg.seq_cfg.op_readonly_on_info1_partition) {
      flash_op.partition == FlashPartInfo1 ->
        flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }

    if (flash_op.partition == FlashPartInfo2) {
        flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }

    flash_op.op inside {[flash_ctrl_pkg::FlashOpRead : flash_ctrl_pkg::FlashOpErase]};
    (flash_op.op == flash_ctrl_pkg::FlashOpErase) ->
    flash_op.erase_type dist {
      flash_ctrl_pkg::FlashErasePage :/ (100 - cfg.seq_cfg.op_erase_type_bank_pc),
      flash_ctrl_pkg::FlashEraseBank :/ cfg.seq_cfg.op_erase_type_bank_pc
    };

    flash_op.num_words inside {[10 : FlashNumBusWords - flash_op.addr[TL_AW-1:TL_SZW]]};
    flash_op.num_words <= cfg.seq_cfg.op_max_words;
    flash_op.num_words < FlashPgmRes - flash_op.addr[TL_SZW+:FlashPgmResWidth];
  }

  constraint flash_op_host_rd_c {
    flash_op_host_rd.partition == FlashPartData;
    flash_op_host_rd.num_words inside {[10 : FlashNumBusWords -
                                        flash_op_host_rd.addr[TL_AW-1:TL_SZW]]};
    flash_op_host_rd.num_words <= cfg.seq_cfg.op_max_words;
    flash_op_host_rd.num_words < FlashPgmRes - flash_op_host_rd.addr[TL_SZW+:FlashPgmResWidth];
  }

  // Flash ctrl operation data queue - used for programing or reading the flash.
  rand data_q_t flash_op_data;
  constraint flash_op_data_c {
    solve flash_op before flash_op_data;
    if (flash_op.op inside {flash_ctrl_pkg::FlashOpRead, flash_ctrl_pkg::FlashOpProgram}) {
      flash_op_data.size() == flash_op.num_words;
    } else {
      flash_op_data.size() == 0;
    }
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

  // Information partitions memory protection rpages settings.
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
          MuBi4False :/ (100 - cfg.seq_cfg.mp_info_page_he_en_pc[i][j]),
          MuBi4True :/ cfg.seq_cfg.mp_info_page_he_en_pc[i][j]
        };

      }
    }
  }

  // Default flash ctrl region settings.
  rand mubi4_t default_region_read_en;
  rand mubi4_t default_region_program_en;
  rand mubi4_t default_region_erase_en;
  mubi4_t default_region_scramble_en;
  rand mubi4_t default_region_he_en;
  rand mubi4_t default_region_ecc_en;

  constraint default_region_read_en_c {default_region_read_en == MuBi4True;}

  constraint default_region_program_en_c {default_region_program_en == MuBi4True;}

  constraint default_region_erase_en_c {default_region_erase_en == MuBi4True;}

  // Bank erasability.
  rand bit [flash_ctrl_pkg::NumBanks-1:0] bank_erase_en;

  constraint bank_erase_en_c {
    foreach (bank_erase_en[i]) {
      bank_erase_en[i] == 1;
    }
  }

  constraint default_region_he_en_c {
    default_region_he_en dist {
      MuBi4True :/ cfg.seq_cfg.default_region_he_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_he_en_pc)
    };
  }

  constraint default_region_ecc_en_c {default_region_ecc_en == MuBi4False;}

  bit [TL_AW-1:0] read_addr;

  // Single direct read data
  bit [TL_DW-1:0] flash_rd_one_data;

  localparam bit [TL_DW-1:0] ALL_ONES = {TL_DW{1'b1}};

  virtual task body();

    // enable sw rw access
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;

    //disable polling of fifo status for frontdoor write and read
    poll_fifo_status = 0;

    // Scoreboard knob for blocking host reads
    cfg.block_host_rd = 1;

    // Scramble disable
    default_region_scramble_en = MuBi4False;

    //Enable Bank erase
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));

    // 1.Scenario tests on the different banks arbitration
    `uvm_info(`gfn, $sformatf("1.Scenario tests on the different banks arbitration"), UVM_HIGH)
    repeat (num_trans) begin
      // Randomize self
      bank_same = 0;
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `uvm_info(`gfn, $sformatf(
            "RAND FLASH OP bank:%0d bank_rd:%0d num_trans:%0d flash_op:%0p flash_op_data:%0p",
            bank,
            bank_rd,
            num_trans,
            flash_op,
            flash_op_data
      ), UVM_HIGH)
      cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
      cfg.flash_mem_bkdr_init(flash_op_host_rd.partition, FlashMemInitInvalidate);
      if (flash_op.op == flash_ctrl_pkg::FlashOpProgram) begin
        cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));
      end else begin
        cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
      end
      cfg.flash_mem_bkdr_write(.flash_op(flash_op_host_rd), .scheme(FlashMemInitRandomize));
      do_operations();
    end

    // 2.Scenario tests on the same bank arbitration
    `uvm_info(`gfn, $sformatf("2.Scenario tests on the same bank arbitration"), UVM_HIGH)
    repeat (num_trans) begin
      // Randomize self
      bank_same = 1;
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `uvm_info(`gfn, $sformatf(
            "RAND FLASH OP bank:%0d bank_rd:%0d num_trans:%0d flash_op:%0p flash_op_data:%0p",
            bank,
            bank_rd,
            num_trans,
            flash_op,
            flash_op_data
      ), UVM_HIGH)
      cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
      cfg.flash_mem_bkdr_init(flash_op_host_rd.partition, FlashMemInitInvalidate);
      if (flash_op.op == flash_ctrl_pkg::FlashOpProgram) begin
        cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));
      end else begin
        cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
      end
      cfg.flash_mem_bkdr_write(.flash_op(flash_op_host_rd), .scheme(FlashMemInitRandomize));
      do_operations();
    end

    // 3.Scenario tests lost of priority of host read on same bank
    `uvm_info(`gfn, $sformatf("3.Scenario tests lost of priority of host read on same bank"),
              UVM_HIGH)

    // start host reads and controller program
    `DV_CHECK_RANDOMIZE_FATAL(this)
    flash_op.partition = FlashPartData;
    flash_op_host_rd.addr = 0;
    flash_op_host_rd.num_words = 30;
    flash_op.op = flash_ctrl_pkg::FlashOpProgram;
    flash_op.addr = 'h14;
    flash_op.num_words = 10;
    cfg.flash_mem_bkdr_init(flash_op_host_rd.partition, FlashMemInitInvalidate);
    cfg.flash_mem_bkdr_write(.flash_op(flash_op_host_rd), .scheme(FlashMemInitSet));
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flash_op_data, flash_op_data.size() == flash_op.num_words;)
    `uvm_info(`gfn, $sformatf("FLASH OP PROGRAM:%0p DATA:%0p", flash_op, flash_op_data), UVM_HIGH)
    do_arb();
  endtask : body

  virtual task do_operations();
    // Configure the flash
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

    // Host direct read of random written value
    `uvm_info(`gfn, $sformatf("Starting direct back-to-back reads and controller operations"),
              UVM_HIGH)
    fork
      begin
        // host read data and init of selected chunk of memory
        host_read_op_data(flash_op_host_rd);
      end
      begin
        // controller read, program or erase
        if (flash_op.op == flash_ctrl_pkg::FlashOpRead) begin
          controller_read_op_data(flash_op);
        end else if (flash_op.op == flash_ctrl_pkg::FlashOpProgram) begin
          controller_program_data(flash_op, flash_op_data);
        end else begin  //flash_op.op == flash_ctrl_pkg::FlashOpErase
          controller_program_erase(flash_op);
        end
      end
    join;
  endtask : do_operations

  // host read data.
  virtual task host_read_op_data(flash_op_t flash_op);
    logic [TL_DW-1:0] rdata;
    for (int j = 0; j < flash_op.num_words; j++) begin
      read_addr = flash_op.addr + 4 * j;
      do_direct_read(.addr(read_addr), .mask('1), .blocking(cfg.block_host_rd), .check_rdata(0),
                     .rdata(rdata));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
    end
  endtask : host_read_op_data

  // Controller read data.
  virtual task controller_read_op_data(flash_op_t flash_op);
    flash_rd_data.delete();
    flash_ctrl_start_op(flash_op);
    flash_ctrl_read(flash_op.num_words, flash_rd_data, poll_fifo_status);
    wait_flash_op_done();
    `uvm_info(`gfn, $sformatf("FLASH OP READ DATA: %0p", flash_rd_data), UVM_HIGH)
    cfg.flash_mem_bkdr_read_check(flash_op, flash_rd_data);
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
  endtask : controller_read_op_data

  // Controller program data.
  virtual task controller_program_data(flash_op_t flash_op, data_q_t flash_op_data);
    data_q_t exp_data;
    exp_data = cfg.calculate_expected_data(flash_op, flash_op_data);
    flash_ctrl_start_op(flash_op);
    flash_ctrl_write(flash_op_data, poll_fifo_status);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
    `uvm_info(`gfn, $sformatf("FLASH OP PROGRAM DATA: %0p", flash_op_data), UVM_HIGH)
    cfg.flash_mem_bkdr_read_check(flash_op, exp_data);
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
  endtask : controller_program_data

  // Controller erase data.
  virtual task controller_program_erase(flash_op_t flash_op);
    data_q_t exp_data;
    exp_data = cfg.calculate_expected_data(flash_op, flash_op_data);
    flash_ctrl_start_op(flash_op);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
    `uvm_info(`gfn, $sformatf("FLASH OP ERASE DATA DONE"), UVM_HIGH)
    cfg.flash_mem_bkdr_erase_check(flash_op, exp_data);
  endtask : controller_program_erase

  virtual task do_arb();
    logic [TL_DW-1:0] rdata;
    data_q_t exp_data;

    // setting non blocking host reads
    cfg.block_host_rd = 0;

    // Configure the flash
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

    `uvm_info(`gfn, $sformatf("Starting arbitration"), UVM_HIGH)

    fork
      begin  // host read data
        `uvm_info(`gfn, $sformatf("FLASH OP HOST RD ARB: %0p", flash_op_host_rd), UVM_HIGH)
        cfg.clk_rst_vif.wait_clks(32);
        for (int j = 0; j < flash_op_host_rd.num_words; j++) begin
          read_addr = flash_op_host_rd.addr + 4 * j;
          do_direct_read(.addr(read_addr), .mask('1), .blocking(cfg.block_host_rd),
                         .check_rdata(0), .rdata(rdata));
          `uvm_info(`gfn, $sformatf("FINISH SENDING HOST ADD: %0d", read_addr), UVM_HIGH)
        end
        csr_utils_pkg::wait_no_outstanding_access();
      end
      begin  // controller program data
        `uvm_info(`gfn, $sformatf("FLASH OP PROGRAM ARB: %0p DATA: %0p", flash_op, flash_op_data),
                  UVM_HIGH)
          exp_data = cfg.calculate_expected_data(flash_op, flash_op_data);
          flash_ctrl_start_op(flash_op);
          flash_ctrl_write(flash_op_data, poll_fifo_status);
          wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
          `uvm_info(`gfn, $sformatf("FINISH PROGRAM ADD: %0d expected:", flash_op.addr), UVM_HIGH)
          cfg.flash_mem_bkdr_read_check(flash_op, exp_data);
      end
    join;

    // check 6th host direct read data after losing priority
    for (int j = 0; j < flash_op_host_rd.num_words; j++) begin
      flash_rd_one_data = cfg.flash_rd_data.pop_front();
      `uvm_info(`gfn, $sformatf("FLASH DIRECT READ DATA: 0x%0h", flash_rd_one_data), UVM_HIGH)
      //first 5 data have init value while 6th value is overwritten by ctrl due to priority lost
      if (j < 5) begin
        `DV_CHECK_EQ(flash_rd_one_data, ALL_ONES)
      end
      if (j == 5) begin
        `DV_CHECK_EQ(flash_rd_one_data, flash_op_data[0])
      end
    end

  endtask : do_arb

endclass : flash_ctrl_phy_arb_vseq
