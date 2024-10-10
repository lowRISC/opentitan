// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// fifo eviction test: read/program/read, read/erase/read
class flash_ctrl_rd_buff_evict_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_rd_buff_evict_vseq)

  `uvm_object_new

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();

    // Do no more than 16 words per op.
    cfg.seq_cfg.op_max_words            = 16;

    // no overlap mp regions
    cfg.seq_cfg.allow_mp_region_overlap = 0;

    // enable high endurance
    cfg.seq_cfg.mp_region_he_en_pc      = 50;
    cfg.seq_cfg.default_region_he_en_pc = 50;
  endfunction

  // Randomized flash ctrl operation.
  rand flash_op_t flash_op;

  rand uint bank;

  bit poll_fifo_status;

  // Constraint address to be in relevant range for the selected partition.
  constraint addr_c {
    solve bank before flash_op;
    bank inside {[0 : flash_ctrl_pkg::NumBanks - 1]};
    flash_op.addr inside {[BytesPerBank * bank : BytesPerBank * (bank + 1) - BytesPerBank / 2]};
  }

  constraint flash_op_c {
    flash_op.erase_type dist {
      flash_ctrl_pkg::FlashErasePage :/ (100 - cfg.seq_cfg.op_erase_type_bank_pc),
      flash_ctrl_pkg::FlashEraseBank :/ cfg.seq_cfg.op_erase_type_bank_pc
    };

    flash_op.partition == FlashPartData;
    flash_op.num_words inside {[10 : FlashNumBusWords - flash_op.addr[TL_AW-1:TL_SZW]]};
    flash_op.num_words <= cfg.seq_cfg.op_max_words;
    flash_op.num_words < FlashPgmRes - flash_op.addr[TL_SZW+:FlashPgmResWidth];
  }

  // Flash ctrl operation data queue - used for programming or reading.
  rand data_q_t flash_op_data;
  data_q_t flash_rd_data;

  // Single host read data
  data_t flash_rd_one_data;

  constraint flash_op_data_c {
    solve flash_op before flash_op_data;
    flash_op_data.size() == flash_op.num_words;
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

      mp_regions[i].he_en dist {
        MuBi4False :/ (100 - cfg.seq_cfg.mp_region_he_en_pc),
        MuBi4True  :/ cfg.seq_cfg.mp_region_he_en_pc
      };
      mp_regions[i].ecc_en == MuBi4False;

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

  // Bank erasability.
  rand bit [flash_ctrl_pkg::NumBanks-1:0] bank_erase_en;

  constraint bank_erase_en_c {
    foreach (bank_erase_en[i]) {
      bank_erase_en[i] == 1;
    }
  }

  // Default flash ctrl region settings.
  mubi4_t default_region_read_en;
  mubi4_t default_region_program_en;
  mubi4_t default_region_erase_en;
  mubi4_t default_region_scramble_en;
  mubi4_t default_region_ecc_en;
  rand mubi4_t default_region_he_en;

  constraint default_region_he_en_c {
    default_region_he_en dist {
      MuBi4False :/ cfg.seq_cfg.default_region_he_en_pc,
      MuBi4True  :/ (100 - cfg.seq_cfg.default_region_he_en_pc)
    };
  }

  addr_t read_addr;
  data_q_t exp_data;
  data_4s_t all_ones = {TL_DW{1'b1}};

  task body();
    int func_cov_op;
    //enable polling of fifo status for frontdoor write and read
    poll_fifo_status           = 1;

    // Default region settings
    default_region_read_en     = MuBi4True;
    default_region_program_en  = MuBi4True;
    default_region_erase_en    = MuBi4True;
    default_region_ecc_en      = MuBi4False;
    default_region_scramble_en = MuBi4False;

    // Scoreboard knob
    cfg.block_host_rd          = 1;

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

    //Enable Bank erase
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));

    // 1. host read, program and host read
    `uvm_info(`gfn, $sformatf("Scenario 1: host read, program and host read"), UVM_HIGH)

    if (!randomize(flash_op, flash_op_data)) begin
      `uvm_fatal(`gfn, "Randomization failed for flash_op & flash_op_data!")
    end

    // Invalidate the flash mem contents. We do this because we operate on and check a specific
    // chunk of space. The rest of the flash mem is essentially dont-care. If the flash ctrl
    // does not work correctly, the check will result in an access from the invalidated mem
    // region exposing the issue.
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
    `uvm_info(`gfn, $sformatf("Starting backdoor write operation with random values"), UVM_HIGH)
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));

    // host read data
    host_read_op_data(flash_op);

    `uvm_info(`gfn, $sformatf("FLASH OP: %0p, BANK %0d", flash_op, bank), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH READ DATA: %0p", exp_data), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH PROGRAM DATA: %0p", flash_op_data), UVM_HIGH)

    // make sure that program data are different then previously read data
    check_diff(flash_op_data);

    // program data
    controller_program_data(flash_op, flash_op_data);

    // host read data has been checked in scoreboard by backdoor read for scramble disabled
    `uvm_info(`gfn, $sformatf("Starting host read after program"), UVM_HIGH)
    host_read_op_data(flash_op);

    // 2. Controller read, program and Controller read
    `uvm_info(`gfn, $sformatf("Scenario 2: Controller read, program and Controller read"), UVM_HIGH)

    if (!randomize(flash_op, flash_op_data)) begin
      `uvm_fatal(`gfn, "Randomization failed for flash_op & flash_op_data!")
    end

    // controller read data and init of selected chunk of memory
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
    controller_read_op_data(flash_op);

    `uvm_info(`gfn, $sformatf("FLASH OP: %0p, BANK %0d", flash_op, bank), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH READ DATA: %0p", flash_rd_data), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH PROGRAM DATA: %0p", flash_op_data), UVM_HIGH)

    // make sure that program data are different then previously read data
    check_diff(flash_op_data);

    // program data
    controller_program_data(flash_op, flash_op_data);

    // controller read data
    controller_read_op_data(flash_op);

    // check Controller read data via backdoor read
    `uvm_info(`gfn, $sformatf("READ FLASH OP PROGRAM/READ DATA: %0p", flash_rd_data), UVM_HIGH)
    cfg.flash_mem_bkdr_read_check(flash_op, flash_rd_data);

    // 3. Controller read, program and host read
    `uvm_info(`gfn, $sformatf("Scenario 3: Controller read, program and host read"), UVM_HIGH)

    if (!randomize(flash_op, flash_op_data)) begin
      `uvm_fatal(`gfn, "Randomization failed for flash_op & flash_op_data!")
    end

    // controller read data and init of selected chunk of memory
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
    controller_read_op_data(flash_op);

    `uvm_info(`gfn, $sformatf("FLASH OP: %0p, BANK %0d", flash_op, bank), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH READ DATA: %0p", flash_rd_data), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH PROGRAM DATA: %0p", flash_op_data), UVM_HIGH)

    // make sure that program data are different then previously read data
    check_diff(flash_op_data);

    // program data
    controller_program_data(flash_op, flash_op_data);

    // host read data
    `uvm_info(`gfn, $sformatf("Starting host read after program"), UVM_HIGH)
    host_read_op_data(flash_op);

    // 4. host read, program and Controller read
    `uvm_info(`gfn, $sformatf("Scenario 4: host read, program and Controller read"), UVM_HIGH)

    if (!randomize(flash_op, flash_op_data)) begin
      `uvm_fatal(`gfn, "Randomization failed for flash_op & flash_op_data!")
    end

    // host read data and init of selected chunk of memory
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
    host_read_op_data(flash_op);

    `uvm_info(`gfn, $sformatf("FLASH OP: %0p, BANK %0d", flash_op, bank), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH READ DATA: %0p", exp_data), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH PROGRAM DATA: %0p", flash_op_data), UVM_HIGH)

    // make sure that program data are different then previously read data
    check_diff(flash_op_data);

    // program data
    controller_program_data(flash_op, flash_op_data);

    // controller read data
    controller_read_op_data(flash_op);

    // check Controller read data via backdoor read
    `uvm_info(`gfn, $sformatf("READ FLASH OP PROGRAM/READ DATA: %0p", flash_rd_data), UVM_HIGH)
    cfg.flash_mem_bkdr_read_check(flash_op, flash_rd_data);

    // 5. host read, erase and host read
    `uvm_info(`gfn, $sformatf("Scenario 5: host read, erase and host read"), UVM_HIGH)

    if (!randomize(flash_op, flash_op_data)) begin
      `uvm_fatal(`gfn, "Randomization failed for flash_op & flash_op_data!")
    end

    // host read data and init of selected chunk of memory
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
    host_read_op_data(flash_op);

    `uvm_info(`gfn, $sformatf("FLASH OP: %0p, BANK %0d", flash_op, bank), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH READ DATA: %0p", exp_data), UVM_HIGH)

    // erase data
    erase_data(flash_op);

    // host data
    `uvm_info(`gfn, $sformatf("Starting host read after program"), UVM_HIGH)
    host_read_op_data(flash_op);

    // make sure that host read data is all ones
    check_all_ones_host();

    // 6. Controller read, erase and Controller read
    `uvm_info(`gfn, $sformatf("Scenario 6: Controller read, erase and Controller read"), UVM_HIGH)

    if (!randomize(flash_op, flash_op_data)) begin
      `uvm_fatal(`gfn, "Randomization failed for flash_op & flash_op_data!")
    end

    // controller read data and init of selected chunk of memory
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
    controller_read_op_data(flash_op);

    `uvm_info(`gfn, $sformatf("FLASH OP: %0p, BANK %0d", flash_op, bank), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH READ DATA: %0p", flash_rd_data), UVM_HIGH)

    // erase data
    erase_data(flash_op);

    // controller read data
    controller_read_op_data(flash_op);

    // check Controller read data via backdoor read
    `uvm_info(`gfn, $sformatf("READ FLASH OP PROGRAM/READ DATA: %0p", flash_rd_data), UVM_HIGH)
    cfg.flash_mem_bkdr_read_check(flash_op, flash_rd_data);

    // make sure that controller read data is all ones
    check_all_ones_ctrl();

    // 7. Controller read, erase and host read
    `uvm_info(`gfn, $sformatf("Scenario 7: Controller read, erase and host read"), UVM_HIGH)

    if (!randomize(flash_op, flash_op_data)) begin
      `uvm_fatal(`gfn, "Randomization failed for flash_op & flash_op_data!")
    end

    // controller read data and init of selected chunk of memory
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
    controller_read_op_data(flash_op);

    `uvm_info(`gfn, $sformatf("FLASH OP: %0p, BANK %0d", flash_op, bank), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH READ DATA: %0p", flash_rd_data), UVM_HIGH)

    // erase data
    erase_data(flash_op);

    // host data
    `uvm_info(`gfn, $sformatf("Starting host read after program"), UVM_HIGH)
    host_read_op_data(flash_op);

    // make sure that host read data is all ones
    check_all_ones_host();

    // 8. host read, erase and Controller read
    `uvm_info(`gfn, $sformatf("Scenario 8: host read, erase and Controller read"), UVM_HIGH)
    if (!randomize(flash_op, flash_op_data)) begin
      `uvm_fatal(`gfn, "Randomization failed for flash_op & flash_op_data!")
    end

    // host read data and init of selected chunk of memory
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
    host_read_op_data(flash_op);

    `uvm_info(`gfn, $sformatf("FLASH OP: %0p, BANK %0d", flash_op, bank), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH READ DATA: %0p", exp_data), UVM_HIGH)

    // erase data
    erase_data(flash_op);

    // controller read data
    controller_read_op_data(flash_op);

    // check Controller read data via backdoor read
    `uvm_info(`gfn, $sformatf("READ FLASH OP PROGRAM/READ DATA: %0p", flash_rd_data), UVM_HIGH)
    cfg.flash_mem_bkdr_read_check(flash_op, flash_rd_data);

    // make sure that controller read data is all ones
    check_all_ones_ctrl();

    // checking coverpoints for state transitions
    if (cfg.en_cov) begin
      func_cov_op = cov.control_cg.op_evict_cp.get_coverage();
      if (func_cov_op == 100) begin
        `uvm_info(`gfn, $sformatf("Coverage READ/PROGRAM(ERASE)/READ reached!"), UVM_LOW)
      end else begin
        `uvm_error(`gfn, $sformatf("Coverage READ/PROGRAM(ERASE)/READ not reached!"))
      end
    end

  endtask : body

  // host read data.
  virtual task host_read_op_data(flash_op_t flash_op);
    data_4s_t rdata;
    bit completed;
    exp_data.delete();
    for (int j = 0; j < flash_op.num_words; j++) begin
      read_addr = flash_op.addr + 4 * j;
      do_direct_read(.addr(read_addr), .mask('1), .blocking(1), .check_rdata(0), .rdata(rdata),
                     .completed(completed));
      exp_data.push_back(rdata);
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
    end
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
  endtask : host_read_op_data

  // Controller read data.
  virtual task controller_read_op_data(ref flash_op_t flash_op);
    flash_op.op = flash_ctrl_pkg::FlashOpRead;
    flash_rd_data.delete();
    flash_ctrl_start_op(flash_op);
    flash_ctrl_read(flash_op.num_words, flash_rd_data, poll_fifo_status);
    wait_flash_op_done();
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
  endtask : controller_read_op_data

  // Controller program data.
  virtual task controller_program_data(ref flash_op_t flash_op, data_q_t flash_op_data);
    flash_op.op = flash_ctrl_pkg::FlashOpProgram;
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));
    flash_ctrl_start_op(flash_op);
    flash_ctrl_write(flash_op_data, poll_fifo_status);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
  endtask : controller_program_data

  // Erase data.
  virtual task erase_data(ref flash_op_t flash_op);
    flash_op.op = flash_ctrl_pkg::FlashOpErase;
    flash_ctrl_start_op(flash_op);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
  endtask : erase_data

  // make sure that program data are different then previously read data
  virtual task check_diff(data_q_t flash_op_data);
    foreach (flash_op_data[k]) begin
      `uvm_info(`gfn, $sformatf(
                "FLASH WRITE DATA: 0x%0h FLASH HOST READ DATA: 0x%0h", flash_op_data[k], exp_data[k]
                ), UVM_HIGH)
      if (flash_op_data[k] == exp_data[k]) begin
        `uvm_error(`gfn, $sformatf(
                   "write_data: 0x%0h == read_data: 0x%0h", flash_op_data[k], exp_data[k]))
      end
    end
  endtask : check_diff

  // make sure that host read data is all ones
  virtual task check_all_ones_host();
    foreach (exp_data[k]) begin
      `uvm_info(`gfn, $sformatf("FLASH HOST READ DATA: 0x%0h", exp_data[k]), UVM_HIGH)
      if (exp_data[k] != all_ones) begin
        `uvm_error(`gfn, $sformatf(
                   "Erased data different than ones: 0x%0h 0x%0h", exp_data[k], all_ones))
      end
    end
  endtask : check_all_ones_host

  // make sure that controller read data is all ones
  virtual task check_all_ones_ctrl();
    foreach (flash_rd_data[k]) begin
      `uvm_info(`gfn, $sformatf("FLASH READ DATA: 0x%0h", flash_rd_data[k]), UVM_HIGH)
      if (flash_rd_data[k] != all_ones) begin
        `uvm_error(`gfn, $sformatf(
                   "Erased data different than ones: 0x%0h 0x%0h", flash_rd_data[k], all_ones))
      end
    end
  endtask : check_all_ones_ctrl

endclass : flash_ctrl_rd_buff_evict_vseq
