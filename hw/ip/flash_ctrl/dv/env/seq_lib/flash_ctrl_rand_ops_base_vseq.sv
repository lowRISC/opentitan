// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This vseq randomly programs memory protection and performs a bunch of read / program / erase
// operations. It is encouraged to extend this vseq to a custom vseq that constrains the
// randomization by overriding the `configure_vseq()` function. See `flash_ctrl_smoke_vseq` for
// example.
class flash_ctrl_rand_ops_base_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_rand_ops_base_vseq)

  // Number of times we run a random flash operation with a fully configured flash ctrl.
  rand uint num_flash_ops_per_cfg;

  constraint num_flash_ops_per_cfg_c {
    num_flash_ops_per_cfg inside {[1 : cfg.seq_cfg.max_flash_ops_per_cfg]};
  }

  // A single randomized flash ctrl operation.
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
    flash_op.op inside {FlashOpRead, FlashOpProgram, FlashOpErase};
    flash_op.addr inside {[0 : FlashSizeBytes - 1]};

    if (!cfg.seq_cfg.op_allow_invalid) {flash_op.op != flash_ctrl_pkg::FlashOpInvalid;}

    if (cfg.seq_cfg.flash_only_op != flash_ctrl_pkg::FlashOpInvalid) {
      flash_op.op == cfg.seq_cfg.flash_only_op;
    }

    (flash_op.op == flash_ctrl_pkg::FlashOpErase) ->
    flash_op.erase_type dist {
      flash_ctrl_pkg::FlashErasePage :/ (100 - cfg.seq_cfg.op_erase_type_bank_pc),
      flash_ctrl_pkg::FlashEraseBank :/ cfg.seq_cfg.op_erase_type_bank_pc
    };

    flash_op.prog_sel dist {
      FlashProgSelNormal :/ (100 - cfg.seq_cfg.op_prog_type_repair_pc),
      FlashProgSelRepair :/ cfg.seq_cfg.op_prog_type_repair_pc
    };

    flash_op.partition dist {
      FlashPartData  :/ cfg.seq_cfg.op_on_data_partition_pc,
      FlashPartInfo  :/ cfg.seq_cfg.op_on_info_partition_pc,
      FlashPartInfo1 :/ cfg.seq_cfg.op_on_info1_partition_pc,
      FlashPartInfo2 :/ cfg.seq_cfg.op_on_info2_partition_pc
    };

    // Bank erase is supported only for data & 1st info partitions
    flash_op.partition != FlashPartData && flash_op.partition != FlashPartInfo ->
    flash_op.erase_type == flash_ctrl_pkg::FlashErasePage;

    if (cfg.seq_cfg.op_readonly_on_info_partition) {
      flash_op.partition == FlashPartInfo -> flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }
    if (cfg.seq_cfg.op_readonly_on_info1_partition) {
      flash_op.partition == FlashPartInfo1 -> flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }

    if (flash_op.op inside {flash_ctrl_pkg::FlashOpRead, flash_ctrl_pkg::FlashOpProgram}) {
      flash_op.num_words inside {[1 : FlashNumBusWords - flash_op.addr[TL_AW-1:TL_SZW]]};
      flash_op.num_words <= cfg.seq_cfg.op_max_words;
      // end of transaction must be within the program resolution
      // units             words         bytes
      flash_op.num_words < FlashPgmRes - flash_op.addr[TL_SZW+:FlashPgmResWidth];
    }

  }

  // Flash ctrl operation data queue - used for programing or reading the flash.
  rand data_q_t             flash_op_data;
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

      mp_regions[i].read_en dist {
        MuBi4False :/ (100 - cfg.seq_cfg.mp_region_read_en_pc),
        MuBi4True  :/ cfg.seq_cfg.mp_region_read_en_pc
      };

      mp_regions[i].program_en dist {
        MuBi4False :/ (100 - cfg.seq_cfg.mp_region_program_en_pc),
        MuBi4True  :/ cfg.seq_cfg.mp_region_program_en_pc
      };

      mp_regions[i].erase_en dist {
        MuBi4False :/ (100 - cfg.seq_cfg.mp_region_erase_en_pc),
        MuBi4True  :/ cfg.seq_cfg.mp_region_erase_en_pc
      };

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

  // Default flash ctrl region settings.
  rand mubi4_t default_region_read_en;
  rand mubi4_t default_region_program_en;
  rand mubi4_t default_region_erase_en;

  constraint default_region_read_en_c {
    default_region_read_en dist {
      MuBi4True  :/ cfg.seq_cfg.default_region_read_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_read_en_pc)
    };
  }

  constraint default_region_program_en_c {
    default_region_program_en dist {
      MuBi4True  :/ cfg.seq_cfg.default_region_program_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_program_en_pc)
    };
  }

  constraint default_region_erase_en_c {
    default_region_erase_en dist {
      MuBi4True :/ cfg.seq_cfg.default_region_erase_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_erase_en_pc)
    };
  }

  // Information partitions memory protection rpages settings.
  rand
  flash_bank_mp_info_page_cfg_t
  mp_info_pages[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes][$];

  constraint mp_info_pages_c {

    foreach (mp_info_pages[i, j]) {

      mp_info_pages[i][j].size() == flash_ctrl_pkg::InfoTypeSize[j];

      foreach (mp_info_pages[i][j][k]) {

        mp_info_pages[i][j][k].en dist {
          MuBi4False :/ (100 - cfg.seq_cfg.mp_info_page_en_pc[i][j]),
          MuBi4True  :/ cfg.seq_cfg.mp_info_page_en_pc[i][j]
        };

        mp_info_pages[i][j][k].read_en dist {
          MuBi4False :/ (100 - cfg.seq_cfg.mp_info_page_read_en_pc[i][j]),
          MuBi4True  :/ cfg.seq_cfg.mp_info_page_read_en_pc[i][j]
        };

        mp_info_pages[i][j][k].program_en dist {
          MuBi4False :/ (100 - cfg.seq_cfg.mp_info_page_program_en_pc[i][j]),
          MuBi4True  :/ cfg.seq_cfg.mp_info_page_program_en_pc[i][j]
        };

        mp_info_pages[i][j][k].erase_en dist {
          MuBi4False :/ (100 - cfg.seq_cfg.mp_info_page_erase_en_pc[i][j]),
          MuBi4True  :/ cfg.seq_cfg.mp_info_page_erase_en_pc[i][j]
        };

        mp_info_pages[i][j][k].scramble_en dist {
          MuBi4False :/ (100 - cfg.seq_cfg.mp_info_page_scramble_en_pc[i][j]),
          MuBi4True  :/ cfg.seq_cfg.mp_info_page_scramble_en_pc[i][j]
        };

        mp_info_pages[i][j][k].ecc_en dist {
          MuBi4False :/ (100 - cfg.seq_cfg.mp_info_page_ecc_en_pc[i][j]),
          MuBi4True  :/ cfg.seq_cfg.mp_info_page_ecc_en_pc[i][j]
        };

        mp_info_pages[i][j][k].he_en dist {
          MuBi4False :/ (100 - cfg.seq_cfg.mp_info_page_he_en_pc[i][j]),
          MuBi4True  :/ cfg.seq_cfg.mp_info_page_he_en_pc[i][j]
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
      0                     :/ 1,
      [1:4]                 :/ 1,
      [5:10]                :/ 1,
      [11:ProgFifoDepth-2]  :/ 1,
      ProgFifoDepth-1       :/ 1
    };
  }

  constraint program_fifo_intr_level_max_c {
    program_fifo_intr_level < ProgFifoDepth;
  }

  constraint read_fifo_intr_level_c {
    read_fifo_intr_level dist {
      0                     :/ 1,
      [1:4]                 :/ 1,
      [5:10]                :/ 1,
      [11:ReadFifoDepth-2]  :/ 1,
      ReadFifoDepth-1       :/ 1
    };
  }

  constraint read_fifo_intr_level_max_c {
    read_fifo_intr_level < ReadFifoDepth;
  }

  // Indicates whether to poll before writing to prog_fifo or reading from rd_fifo. If interupts are
  // enabled, the interrupt signals will be used instead. When set to 0, it will continuously write
  // to prog_fifo / read from rd_fifo, relying on their natural backpressure mechanism.
  rand bit poll_fifo_status;

  constraint poll_fifo_status_c {
    poll_fifo_status dist {
      0 :/ (100 - cfg.seq_cfg.poll_fifo_status_pc),
      1 :/ cfg.seq_cfg.poll_fifo_status_pc
    };
  }

  `uvm_object_new

  task body();
    rd_cache_t rd_entry;
    bit op_ok = 0;
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::On;
    cfg.scb_check                               = 1;
    for (int i = 1; i <= num_trans; i++) begin
      `uvm_info(`gfn, $sformatf("Configuring flash_ctrl %0d/%0d", i, num_trans), UVM_MEDIUM)

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

      flash_ctrl_default_region_cfg(.read_en(default_region_read_en),
                                    .program_en(default_region_program_en),
                                    .erase_en(default_region_erase_en));

      foreach (mp_info_pages[i, j, k]) begin
        flash_ctrl_mp_info_page_cfg(i, j, k, mp_info_pages[i][j][k]);
      end

      flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));

      // Send num_flash_ops_per_cfg number of ops with this configuration.
      for (int j = 1; j <= num_flash_ops_per_cfg; j++) begin
        data_q_t exp_data;
        int retry_cnt = 0;
        // Those 2 has to be randomized simultaneously, otherwise the value of flash_op_data from
        //  the previous iteration will affect the randomization of flash_op.
        while (op_ok == 0 && retry_cnt < 100) begin
          if (!randomize(flash_op, flash_op_data)) begin
            `uvm_fatal(`gfn, "Randomization failed for flash_op & flash_op_data!")
          end
          rd_entry.bank = flash_op.addr[OTFBankId];
          flash_op.otf_addr = flash_op.addr[OTFBankId-1:0];
          rd_entry.addr = flash_op.otf_addr;
          rd_entry.addr[2:0] = 'h0;
          rd_entry.part = flash_op.partition;

          if (flash_op.op == FlashOpRead) begin
            if (!cfg.otf_read_entry.check(rd_entry, flash_op)) begin
              cfg.otf_read_entry.insert(rd_entry, flash_op);
              op_ok = 1;
            end
          end else begin
            op_ok = 1;
            cfg.otf_read_entry.update(rd_entry, flash_op);
          end
          retry_cnt++;
        end
        op_ok = 0;
        `uvm_info(`gfn, $sformatf(
                  "Starting flash_ctrl op: %0d/%0d: %p", j, num_flash_ops_per_cfg, flash_op),
                  UVM_LOW)

        // Bkdr initialize the flash mem based on op.
        // If you wish to do the transaction without the backdoor preperation
        //  (when you want transaction to affect each other), set do_tran_prep_mem to 0.
        if (cfg.seq_cfg.do_tran_prep_mem) flash_ctrl_prep_mem(flash_op);

        flash_ctrl_start_op(flash_op);
        `uvm_info(`gfn, $sformatf(
                  "Wait for operation to be done, then %s (check_mem_post_tran=%0d)",
                  (cfg.seq_cfg.check_mem_post_tran ? "backdoor check the flash" :
                                  "skip to next transaction"),
                  cfg.seq_cfg.check_mem_post_tran
                  ), UVM_HIGH)
        // Calculate expected data for post-transaction checks
        exp_data = cfg.calculate_expected_data(flash_op, flash_op_data);
        case (flash_op.op)
          flash_ctrl_pkg::FlashOpRead: begin
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(poll_fifo_status)
            flash_ctrl_read(flash_op.num_words, flash_op_data, poll_fifo_status);
            wait_flash_op_done();
            if (cfg.seq_cfg.check_mem_post_tran)
              cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);
          end
          flash_ctrl_pkg::FlashOpProgram: begin
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(poll_fifo_status)
            flash_ctrl_write(flash_op_data, poll_fifo_status);
            wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
            if (cfg.seq_cfg.check_mem_post_tran) cfg.flash_mem_bkdr_read_check(flash_op, exp_data);
          end
          flash_ctrl_pkg::FlashOpErase: begin
            wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
            if (cfg.seq_cfg.check_mem_post_tran) cfg.flash_mem_bkdr_erase_check(flash_op, exp_data);
          end
          default: begin
            // FlashOpInvalid
            // covered by flash_ctrl_invalid_op_vseq
          end
        endcase
      end
    end
  endtask : body

  // Prep the flash mem via bkdr before an op for enhanced checks.
  virtual task flash_ctrl_prep_mem(flash_op_t flash_op);
    // Invalidate the flash mem contents. We do this because we operate on and check a specific
    // chunk of space. The rest of the flash mem is essentially dont-care. If the flash ctrl
    // does not work correctly, the check will result in an access from the invalidated mem
    // region exposing the issue.
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
    case (flash_op.op)
      flash_ctrl_pkg::FlashOpRead: begin
        // Initialize the targeted mem region with random data.
        cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
        cfg.clk_rst_vif.wait_clks(1);
      end
      flash_ctrl_pkg::FlashOpProgram: begin
        // Initialize the targeted mem region with all 1s. This is required because the flash
        // needs to be erased to all 1s between each successive programming.
        cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));
      end
    endcase
  endtask

endclass : flash_ctrl_rand_ops_base_vseq
