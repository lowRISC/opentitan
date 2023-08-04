// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Flash invalid operation test. All partitions are exercised
// with final check that invalid operation does not affect flash
// memory content.
class flash_ctrl_invalid_op_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_invalid_op_vseq)

  `uvm_object_new

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();

    // enable high endurance
    cfg.seq_cfg.mp_region_he_en_pc      = 50;
    cfg.seq_cfg.default_region_he_en_pc = 50;

  endfunction

  rand flash_op_t flash_op;
  flash_op_t flash_op_inv;
  flash_op_t flash_op_rd;
  flash_op_t flash_op_er;
  rand data_q_t flash_op_data;
  bit poll_fifo_status;
  int num_trans;
  bit expect_alert;

  constraint flash_op_data_c {
    solve flash_op before flash_op_data;
    flash_op_data.size() == flash_op.num_words;
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
    // Add read only constraint for closed source env
    if (cfg.seq_cfg.op_readonly_on_info_partition) {
      flash_op.partition == FlashPartInfo -> flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }
    if (cfg.seq_cfg.op_readonly_on_info1_partition) {
      flash_op.partition == FlashPartInfo1 -> flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }
    flash_op.addr inside {[0 : FlashSizeBytes - 1]};
    // 8Byte (2 words) aligned.
    // With scramble enabled, odd size of word access (or address) will cause
    // ecc errors.
    flash_op.addr[2:0] == 3'h0;
    flash_op.erase_type == flash_ctrl_pkg::FlashErasePage;
    flash_op.num_words inside {[10 : FlashNumBusWords - flash_op.addr[TL_AW-1:TL_SZW]]};
    flash_op.num_words <= cfg.seq_cfg.op_max_words;
    flash_op.num_words < FlashPgmRes - flash_op.addr[TL_SZW+:FlashPgmResWidth];
    flash_op.num_words % 2 == 0;
  }

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
          MuBi4True  :/ cfg.seq_cfg.mp_region_he_en_pc
        };
      }
    }
  }

  // Default flash ctrl region settings.
  mubi4_t default_region_read_en;
  mubi4_t default_region_program_en;
  mubi4_t default_region_erase_en;
  rand mubi4_t default_region_he_en;
  mubi4_t default_region_scramble_en;
  mubi4_t default_region_ecc_en;

  // Bank erasability.
  bit [flash_ctrl_pkg::NumBanks-1:0] bank_erase_en;

  constraint default_region_he_en_c {
    default_region_he_en dist {
      MuBi4True  :/ cfg.seq_cfg.default_region_he_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_he_en_pc)
    };
  }

  virtual task pre_start();
    super.pre_start();
    // This test requires fast alert hand shake to avoid overlapping
    // multiple alert expected / completed.
    cfg.m_alert_agent_cfgs["recov_err"].ack_delay_max = 1;
    cfg.m_alert_agent_cfgs["recov_err"].ack_stable_max = 1;
  endtask // pre_start

  virtual task body();
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::On;
    cfg.scb_check                               = 1;
    cfg.check_full_scb_mem_model                = 1;
    poll_fifo_status                            = 1;
    num_trans                                   = 100;

    repeat (num_trans) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      do_op();
    end

  endtask : body

  virtual task do_op();

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

    for (int i = 1; i < 4; i++) begin
      mp_info_pages[0][0][i].ecc_en = MuBi4True;
      mp_info_pages[0][0][i].scramble_en = MuBi4True;
    end

    foreach (mp_info_pages[i, j, k]) begin
      flash_ctrl_mp_info_page_cfg(i, j, k, mp_info_pages[i][j][k]);
      `uvm_info(`gfn, $sformatf("MP INFO regions values %p", mp_info_pages[i][j][k]), UVM_HIGH)
    end
    //Enable Bank erase
    bank_erase_en = {NumBanks{1'b1}};
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));
    flash_op.op  = FlashOpProgram;
    flash_op_inv = flash_op;
    flash_op_rd  = flash_op;
    flash_op_er  = flash_op;
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));
    flash_ctrl_start_op(flash_op);
    flash_ctrl_write(flash_op_data, poll_fifo_status);
    wait_flash_op_done(.clear_op_status(0), .timeout_ns(cfg.seq_cfg.prog_timeout_ns));

    expect_alert          = 1;
    cfg.scb_h.expected_alert["recov_err"].expected = 1;
    cfg.scb_h.expected_alert["recov_err"].max_delay = 1000;
    flash_op_inv.op       = FlashOpInvalid;
    flash_ctrl_start_op(flash_op_inv);
    wait_flash_op_done();

    ral.err_code.op_err.predict(expect_alert);
    check_exp_alert_status(expect_alert, "op_err", flash_op_inv, flash_op_data);
    cfg.scb_h.expected_alert["recov_err"].expected = 0;

    flash_op_rd.op = FlashOpRead;
    flash_op_data = {};
    flash_ctrl_start_op(flash_op_rd);
    flash_ctrl_read(flash_op_rd.num_words, flash_op_data, poll_fifo_status);
    wait_flash_op_done();
    flash_op_er.op = FlashOpErase;
    flash_ctrl_start_op(flash_op_er);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));

    flash_op_inv.op = FlashOpInvalid;
    cfg.scb_h.expected_alert["recov_err"].expected = 1;
    flash_ctrl_start_op(flash_op_inv);
    wait_flash_op_done();
    ral.err_code.op_err.predict(expect_alert);
    check_exp_alert_status(expect_alert, "op_err", flash_op_inv, flash_op_data);
    cfg.scb_h.expected_alert["recov_err"].expected = 0;

    flash_op_rd.op = FlashOpRead;
    flash_op_data = {};
    flash_ctrl_start_op(flash_op_rd);
    flash_ctrl_read(flash_op_rd.num_words, flash_op_data, poll_fifo_status);
    wait_flash_op_done();
  endtask : do_op

endclass : flash_ctrl_invalid_op_vseq
