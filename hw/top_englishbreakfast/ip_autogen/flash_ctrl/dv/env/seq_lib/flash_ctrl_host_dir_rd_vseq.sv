// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// host direct back to back read test. Testing pipeline architecture
// of host interface reads with and without scrambling enabled.
class flash_ctrl_host_dir_rd_vseq extends flash_ctrl_fetch_code_vseq;
  `uvm_object_utils(flash_ctrl_host_dir_rd_vseq)

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

  endfunction


  // Constraint address to be in relevant range for the selected partition.
  constraint addr_c {
    solve bank before flash_op;
    flash_op.addr inside {[BytesPerBank * bank : BytesPerBank * (bank + 1) - BytesPerBank / 2]};
  }

  constraint flash_op_c {
    flash_op.op == flash_ctrl_pkg::FlashOpProgram;
    flash_op.partition == FlashPartData;
    flash_op.num_words inside {[10 : FlashNumBusWords - flash_op.addr[TL_AW-1:TL_SZW]]};
    flash_op.num_words <= cfg.seq_cfg.op_max_words;
    flash_op.num_words < FlashPgmRes - flash_op.addr[TL_SZW+:FlashPgmResWidth];
  }

  // Single direct read data
  data_t flash_rd_one_data;

  constraint mp_regions_c {
    solve en_mp_regions before mp_regions;

    foreach (mp_regions[i]) {
      mp_regions[i].en == mubi4_bool_to_mubi(en_mp_regions[i]);

      mp_regions[i].read_en == MuBi4True;

      mp_regions[i].program_en == MuBi4True;

      mp_regions[i].erase_en dist {
        MuBi4False :/ (100 - cfg.seq_cfg.mp_region_erase_en_pc),
        MuBi4True  :/ cfg.seq_cfg.mp_region_erase_en_pc
      };

      mp_regions[i].he_en dist {
        MuBi4False :/ (100 - cfg.seq_cfg.mp_region_he_en_pc),
        MuBi4True  :/ cfg.seq_cfg.mp_region_he_en_pc
      };
      mp_regions[i].ecc_en == MuBi4False;
      mp_regions[i].scramble_en == MuBi4False;

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

  // Default flash ctrl region settings.
  rand mubi4_t default_region_erase_en;

  constraint default_region_erase_en_c {
    default_region_erase_en dist {
      MuBi4True  :/ cfg.seq_cfg.default_region_erase_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_erase_en_pc)
    };
  }

  bit   [TL_AW-1:0] read_addr;
  data_4s_t rdata;
  virtual task body();
    repeat (num_trans) begin
      // Randomize self
      `DV_CHECK_RANDOMIZE_FATAL(this)
      do_tasks();
    end
  endtask : body

  task do_tasks();
    bit comp;
    //enable polling of fifo status for frontdoor write and read
    poll_fifo_status = 1;

    // Scoreboard knob
    cfg.block_host_rd = 1;

    // 1. Scramble disabled, read data has been checked in scoreboard by backdoor read
    // Configure the flash with scramble disable.
    foreach (mp_regions[k]) begin
      flash_ctrl_mp_region_cfg(k, mp_regions[k]);
      `uvm_info(`gfn, $sformatf("MP regions values %p", mp_regions[k]), UVM_HIGH)
    end

    flash_ctrl_default_region_cfg(
        .read_en(default_region_read_en), .program_en(default_region_program_en),
        .erase_en(default_region_erase_en), .scramble_en(default_region_scramble_en),
        .ecc_en(default_region_ecc_en), .he_en(default_region_he_en));

    // Invalidate the flash mem contents. We do this because we operate on and check a specific
    // chunk of space. The rest of the flash mem is essentially dont-care. If the flash ctrl
    // does not work correctly, the check will result in an access from the invalidated mem
    // region exposing the issue.
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
    `uvm_info(`gfn, $sformatf("Starting backdoor write operation with random values"), UVM_HIGH)
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));

    // Host direct read of random written value
    `uvm_info(`gfn, $sformatf("Starting direct back-to-back reads without scramble enabled"),
              UVM_HIGH)

    for (int j = 0; j < flash_op.num_words; j++) begin
      read_addr = flash_op.addr + 4 * j;
      do_direct_read(.addr(read_addr), .mask('1), .blocking(1'b0), .check_rdata(0), .rdata(rdata),
                     .completed(comp));
    end
    csr_utils_pkg::wait_no_outstanding_access();

    // 2. Scramble enabled, host direct read data has been checked by SW read
    `uvm_info(`gfn, $sformatf("Starting direct back-to-back reads with scramble enabled"), UVM_HIGH)

    cfg.block_host_rd = 0;

    // Configure the flash with scramble disable as this particular test does not support it.
    // Configurations where scrambling and ECC are enabled are tested in the *_otf environment.
    foreach (mp_regions[k]) begin
      mp_regions[k].scramble_en = MuBi4False;
      flash_ctrl_mp_region_cfg(k, mp_regions[k]);
      `uvm_info(`gfn, $sformatf("MP regions values %p", mp_regions[k]), UVM_HIGH)
    end

    default_region_scramble_en = MuBi4False;
    flash_ctrl_default_region_cfg(
        .read_en(default_region_read_en), .program_en(default_region_program_en),
        .erase_en(default_region_erase_en), .scramble_en(default_region_scramble_en),
        .ecc_en(default_region_ecc_en), .he_en(default_region_he_en));

    // Start Controller
    `uvm_info(`gfn, $sformatf("FLASH OP: %0p, BANK %0d", flash_op, bank), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("FLASH OP DATA: %0p", flash_op_data), UVM_HIGH)
    flash_ctrl_start_op(flash_op);

    flash_ctrl_write(flash_op_data, poll_fifo_status);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));

    // Select FLASH Read Operation
    flash_op.op = flash_ctrl_pkg::FlashOpRead;

    // Start Controller read data
    flash_ctrl_start_op(flash_op);
    flash_ctrl_read(flash_op.num_words, flash_op_data, poll_fifo_status);
    wait_flash_op_done();
    `uvm_info(`gfn, $sformatf("READ FLASH OP DATA: %0p", flash_op_data), UVM_HIGH)

    for (int j = 0; j < flash_op.num_words; j++) begin
      read_addr = flash_op.addr + 4 * j;
      do_direct_read(.addr(read_addr), .mask('1), .blocking(1'b0), .check_rdata(0), .rdata(rdata),
                     .completed(comp));
    end
    csr_utils_pkg::wait_no_outstanding_access();

    // check SW read data and Host direct read data
    foreach (flash_op_data[k]) begin
      flash_rd_one_data = cfg.flash_rd_data.pop_front();
      `uvm_info(`gfn, $sformatf(
                "FLASH READ DATA: 0x%0h FLASH DIRECT READ DATA: 0x%0h",
                flash_op_data[k],
                flash_rd_one_data
                ), UVM_HIGH)
      `DV_CHECK_EQ(flash_op_data[k], flash_rd_one_data)
    end

    // check directly read data queue
    if (cfg.flash_rd_data.size() != 0) begin
      `uvm_error(`gfn, $sformatf("Queue of read data has:%0d elements!", cfg.flash_rd_data.size()))
    end

  endtask : do_tasks

endclass : flash_ctrl_host_dir_rd_vseq
