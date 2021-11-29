// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic smoke hw  if test vseq
class flash_ctrl_smoke_hw_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_smoke_hw_vseq)

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();
    // Do fewer reruns for the smoke test.
    cfg.seq_cfg.max_num_trans = 1;

    // Do fewer flash ops in each rerun for the smoke test.
    cfg.seq_cfg.max_flash_ops_per_cfg = 1;

    // Do no more than 128 words per op.
    cfg.seq_cfg.op_max_words = 1;

    // Don't enable any memory protection.
    cfg.seq_cfg.num_en_mp_regions = 0;

    // Don't enable access to any of information partitions.
    foreach (cfg.seq_cfg.mp_info_page_en_pc[i, j]) begin
      cfg.seq_cfg.mp_info_page_en_pc[i][j] = 0;
    end

    // Enable default region read/program and erasability.
    cfg.seq_cfg.default_region_read_en_pc = 100;
    cfg.seq_cfg.default_region_program_en_pc = 100;
    cfg.seq_cfg.default_region_erase_en_pc = 100;

    // Allow banks to be erased.
    cfg.seq_cfg.bank_erase_en_pc = 100;

    cfg.seq_cfg.poll_fifo_status_pc = 0;

  endfunction

  // A single PROGRAM flash ctrl operation.
  rand flash_op_t flash_op;

  rand uint bank;

  // Constraint address to be in relevant range for the selected partition.
  constraint addr_c {
    solve bank before flash_op;
    bank == 0;
  }

  constraint flash_op_c {
    flash_op.addr == 0;
    flash_op.op == flash_ctrl_pkg::FlashOpProgram;
    flash_op.partition == FlashPartData;
    flash_op.num_words == 1;
  }

  // Flash ctrl operation data queue - used for programing or reading the flash.
  rand data_q_t flash_op_data;

  constraint flash_op_data_c {
    solve flash_op before flash_op_data;
    flash_op_data.size() == flash_op.num_words;
  }

  // Bit vector representing which of the mp region cfg CSRs to enable.
  rand bit [flash_ctrl_pkg::MpRegions-1:0] en_mp_regions;

  constraint en_mp_regions_c {
    $countones(en_mp_regions) == cfg.seq_cfg.num_en_mp_regions;
  }

  // Memory protection regions settings.
  rand flash_mp_region_cfg_t mp_regions[flash_ctrl_pkg::MpRegions];

  constraint mp_regions_c {
    solve en_mp_regions before mp_regions;

    foreach (mp_regions[i]) {
      mp_regions[i].en == en_mp_regions[i];

      mp_regions[i].read_en dist {
        0 :/ (100 - cfg.seq_cfg.mp_region_read_en_pc),
        1 :/ cfg.seq_cfg.mp_region_read_en_pc
      };

      mp_regions[i].program_en dist {
        0 :/ (100 - cfg.seq_cfg.mp_region_program_en_pc),
        1 :/ cfg.seq_cfg.mp_region_program_en_pc
      };

      mp_regions[i].erase_en dist {
        0 :/ (100 - cfg.seq_cfg.mp_region_erase_en_pc),
        1 :/ cfg.seq_cfg.mp_region_erase_en_pc
      };

      mp_regions[i].start_page inside {[0:FlashNumPages - 1]};
      mp_regions[i].num_pages inside {[1:FlashNumPages - mp_regions[i].start_page]};
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
  rand bit default_region_read_en;
  rand bit default_region_program_en;
  rand bit default_region_erase_en;

  constraint default_region_read_en_c {
    default_region_read_en dist {
      1 :/ cfg.seq_cfg.default_region_read_en_pc,
      0 :/ (100 - cfg.seq_cfg.default_region_read_en_pc)
    };
  }

  constraint default_region_program_en_c {
    default_region_program_en dist {
      1 :/ cfg.seq_cfg.default_region_program_en_pc,
      0 :/ (100 - cfg.seq_cfg.default_region_program_en_pc)
    };
  }

  constraint default_region_erase_en_c {
    default_region_erase_en dist {
      1 :/ cfg.seq_cfg.default_region_erase_en_pc,
      0 :/ (100 - cfg.seq_cfg.default_region_erase_en_pc)
    };
  }

  // Information partitions memory protection rpages settings.
  rand flash_bank_mp_info_page_cfg_t
         mp_info_pages[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes][$];

  constraint mp_info_pages_c {

    foreach (mp_info_pages[i, j]) {

      mp_info_pages[i][j].size() == flash_ctrl_pkg::InfoTypeSize[j];

      foreach (mp_info_pages[i][j][k]) {

        mp_info_pages[i][j][k].en dist {
          0 :/ (100 - cfg.seq_cfg.mp_info_page_en_pc[i][j]),
          1 :/ cfg.seq_cfg.mp_info_page_en_pc[i][j]
        };

        mp_info_pages[i][j][k].read_en dist {
          0 :/ (100 - cfg.seq_cfg.mp_info_page_read_en_pc[i][j]),
          1 :/ cfg.seq_cfg.mp_info_page_read_en_pc[i][j]
        };

        mp_info_pages[i][j][k].program_en dist {
          0 :/ (100 - cfg.seq_cfg.mp_info_page_program_en_pc[i][j]),
          1 :/ cfg.seq_cfg.mp_info_page_program_en_pc[i][j]
        };

        mp_info_pages[i][j][k].erase_en dist {
          0 :/ (100 - cfg.seq_cfg.mp_info_page_erase_en_pc[i][j]),
          1 :/ cfg.seq_cfg.mp_info_page_erase_en_pc[i][j]
        };

      }
    }
  }

  // Bank erasability.
  rand bit [flash_ctrl_pkg::NumBanks-1:0] bank_erase_en;

  constraint bank_erase_en_c {
    foreach (bank_erase_en[i]) {
      bank_erase_en[i] dist {
        0 :/ (100 - cfg.seq_cfg.bank_erase_en_pc),
        1 :/ cfg.seq_cfg.bank_erase_en_pc
      };
    }
  }

  // Fifo levels.
  rand uint program_fifo_intr_level;
  rand uint read_fifo_intr_level;

  constraint program_fifo_intr_level_c {
    program_fifo_intr_level dist {
      0                                 :/ 1,
      [1:4]                             :/ 1,
      [5:10]                            :/ 1,
      [11:flash_ctrl_pkg::FifoDepth-2]  :/ 1,
      flash_ctrl_pkg::FifoDepth-1       :/ 1
    };
  }

  constraint program_fifo_intr_level_max_c {
    program_fifo_intr_level < flash_ctrl_pkg::FifoDepth;
  }

  constraint read_fifo_intr_level_c {
    read_fifo_intr_level dist {
      0                                 :/ 1,
      [1:4]                             :/ 1,
      [5:10]                            :/ 1,
      [11:flash_ctrl_pkg::FifoDepth-2]  :/ 1,
      flash_ctrl_pkg::FifoDepth-1       :/ 1
    };
  }

  constraint read_fifo_intr_level_max_c {
    read_fifo_intr_level < flash_ctrl_pkg::FifoDepth;
  }

  `uvm_object_new

  task body();
    bit [TL_DW-1:0] exp_data;
    bit [TL_DW-1:0] rdata;
    bit [TL_AW-1:0] read_addr;

    `uvm_info(`gfn, $sformatf("Configuring flash_ctrl"), UVM_MEDIUM)

    // If external_cfg=1 it means this sequence is being randomized by another sequence and this
    //  randomization will possibly override the upper randomization (Added specifically for
    //  partner sequences using this one).
    if (!cfg.seq_cfg.external_cfg) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
    end

    // Configure the flash based on the randomized settings.
    foreach (mp_regions[i]) begin
      flash_ctrl_mp_region_cfg(i, mp_regions[i]);
    end

    flash_ctrl_default_region_cfg(.read_en   (default_region_read_en),
                                  .program_en(default_region_program_en),
                                  .erase_en  (default_region_erase_en));

    foreach (mp_info_pages[i, j, k]) begin
      flash_ctrl_mp_info_page_cfg(i, j, k, mp_info_pages[i][j][k]);
    end

    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(flash_op)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(flash_op_data)

    `uvm_info(`gfn, $sformatf("Starting flash_ctrl op backdoor: %p", flash_op), UVM_LOW)
    `uvm_info(`gfn, $sformatf("INIT BEFORE PROGRAM OP"), UVM_HIGH)
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));

    //setting half 1 due to FlashMemInitSet
    exp_data = {{TL_DW/2{1'b0}},{TL_DW/2{1'b1}}};

    // read HW IF

    `uvm_info(`gfn, $sformatf("DIRECT READ via HOST IF on addr %0h", flash_op.addr), UVM_LOW)

    read_hw(flash_op.addr, exp_data);

  endtask : body

  // READ HW IF task
  virtual task read_hw(bit [TL_AW-1:0] raddr, bit [TL_DW-1:0] exp_data);
    cip_tl_host_single_seq read_seq;
    bit [TL_DW-1:0] data;

    `uvm_create_on(read_seq, p_sequencer.eflash_tl_sequencer_h);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(read_seq,
            addr  == raddr;
            write == 0;
            mask == 3;)
    `uvm_send(read_seq)
    data = read_seq.rsp.d_data;
    `uvm_info(`gfn, $sformatf("READ TL DATA: 0x%0h on ADDR: 0x%0h", data, raddr), UVM_HIGH)
    if (data != exp_data) begin
      `uvm_error(`gfn, $sformatf("Received data:%0h is different then expected data:%0h", data,
                 exp_data))
    end
  endtask

endclass : flash_ctrl_smoke_hw_vseq
