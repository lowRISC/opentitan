// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Flash middle operation reset test. Send reset via power ready signal
// in the middle of operation program, read, erase and erase suspend.
class flash_ctrl_mid_op_rst_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_mid_op_rst_vseq)

  `uvm_object_new

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();

    // enable high endurance
    cfg.seq_cfg.mp_region_he_en_pc      = 50;
    cfg.seq_cfg.default_region_he_en_pc = 50;

    // num of words to program
    cfg.seq_cfg.op_max_words            = 4;

  endfunction

  parameter uint   NUM_TRANS = 20;

  rand flash_op_t flash_op;
  flash_op_t      flash_op_q       [NUM_TRANS];
  flash_op_t      flash_op_erase;
  flash_op_t      flash_op_rd;
  rand data_q_t   flash_op_data;
  bit             poll_fifo_status;
  bit             expect_alert;

  // Constraint address to be in relevant range for the selected partition.
  constraint addr_c {
    if (flash_op.partition != FlashPartData) {
      flash_op.addr inside
       {[0:InfoTypeBytes[flash_op.partition>>1]-1],
        [BytesPerBank:BytesPerBank+InfoTypeBytes[flash_op.partition>>1]-1]};
    }
  }

  constraint flash_op_c {
    flash_op.prog_sel == FlashProgSelNormal;
    flash_op.erase_type == flash_ctrl_pkg::FlashErasePage;
    flash_op.addr inside {[0 : FlashSizeBytes - 1]};
    flash_op.num_words inside {[1 : FlashNumBusWords - flash_op.addr[TL_AW-1:TL_SZW]]};
    flash_op.num_words <= cfg.seq_cfg.op_max_words;
    flash_op.num_words < FlashPgmRes - flash_op.addr[TL_SZW+:FlashPgmResWidth];
  }

  constraint flash_op_data_c {
    solve flash_op before flash_op_data;
    flash_op_data.size() == flash_op.num_words;
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

  task pre_start();
    cfg.skip_init_buf_en = 1;
    super.pre_start();
  endtask // pre_start

  virtual task body();
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::On;
    cfg.scb_check                               = 1;
    cfg.check_full_scb_mem_model                = 1;
    poll_fifo_status                            = 1;
    // program interrupt
    for (int i = 0; i < NUM_TRANS; i++) begin
      `DV_CHECK_RANDOMIZE_WITH_FATAL(this, flash_op.op == FlashOpProgram;
                                           flash_op.partition == FlashPartData;)
      flash_op_q[i] = flash_op;
      do_cfg();
      do_prog(flash_op);
      fork
        begin : isolation_fork_prog
          fork
            begin
              cfg.clk_rst_vif.wait_clks(100);
            end
            begin
              cfg.clk_rst_vif.wait_clks(30);
              low_ready_h();
            end
          join_any;
          disable fork;
        end : isolation_fork_prog
      join
      wait_cfg_prog_rd();
    end
    // erase interrupt
    for (int i = 0; i < NUM_TRANS; i++) begin
      do_erase(flash_op_q[i]);
      fork
        begin : isolation_fork_erase
          fork
            begin
              cfg.clk_rst_vif.wait_clks(100);
            end
            begin
              cfg.clk_rst_vif.wait_clks(30);
              low_ready_h();
            end
          join_any;
          disable fork;
        end : isolation_fork_erase
      join
      wait_cfg_prog_rd();
    end

    // erase suspend interrupt
    fork
      begin : isolation_fork_erase_suspend
        fork
          begin
            do_erase(flash_op_q[0]);
            cfg.clk_rst_vif.wait_clks(100);
          end
          begin
            cfg.clk_rst_vif.wait_clks(30);
            csr_wr(.ptr(ral.erase_suspend), .value(1));
            low_ready_h();
          end
        join
      end : isolation_fork_erase_suspend
    join
    wait_cfg_prog_rd();

    // cleaning before full memory check
    for (int i = 0; i < NUM_TRANS; i++) begin
      do_erase(flash_op_q[i]);
      wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
    end

    // read interrupt
    `DV_CHECK_RANDOMIZE_WITH_FATAL(this, flash_op.op == FlashOpRead;
                                         flash_op.partition == FlashPartData;
                                         flash_op.num_words == 1;)
    do_cfg();
    fork
      begin : isolation_fork_read
        fork
          begin
            do_read(flash_op);
            cfg.clk_rst_vif.wait_clks(100);
          end
          begin
            cfg.clk_rst_vif.wait_clks(19);
            low_ready_h();
            apply_reset();
          end
        join
      end : isolation_fork_read
    join
  endtask : body

  // Task to wait and then do random program and read transactions and check that they complete
  //  successfully (and by this making sure the flash recovered from the power-loss)
  task wait_cfg_prog_rd();
    data_q_t exp_data;
    flash_op_t myop;
    // Wait some time to make sure flash is stable again.
    cfg.clk_rst_vif.wait_clks(1_000);
    // Make sure that flash initialization is complete.
    csr_spinwait(.ptr(ral.status.init_wip), .exp_data(1'b0));
    // Make sure to clear the op_status register's done.
    clear_outstanding_done();
    // Configure memry protection.
    do_cfg();
    // Do random program transaction, then check it completed successfully.
    `DV_CHECK_RANDOMIZE_WITH_FATAL(this, flash_op.op == FlashOpProgram;
                                         flash_op.partition == FlashPartData;)
    do_prog(flash_op);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
    exp_data = cfg.calculate_expected_data(flash_op, flash_op_data);
    cfg.flash_mem_bkdr_read_check(flash_op, exp_data);
    cfg.clk_rst_vif.wait_clks(100);
    // Store program op for read back.
    myop = flash_op;

    // Do read back transaction, then check it completed successfully.
    `DV_CHECK_RANDOMIZE_WITH_FATAL(this, flash_op.op == FlashOpRead;
                                         flash_op.addr == myop.addr;
                                         flash_op.partition == FlashPartData;
                                         flash_op.num_words == 1;)
    do_read(flash_op);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.read_timeout_ns));
    cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);
  endtask : wait_cfg_prog_rd

  // Task to clear the op_status register's done before starting the next transaction.
  task clear_outstanding_done();
    uvm_reg_data_t data;
    bit done;
    csr_rd(.ptr(ral.op_status), .value(data));
    done = get_field_val(ral.op_status.done, data);
    if (done) begin
      data = get_csr_val_with_updated_field(ral.op_status.done, data, 0);
      csr_wr(.ptr(ral.op_status), .value(data));
    end
  endtask : clear_outstanding_done

  virtual task do_cfg();

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
    bank_erase_en = {NumBanks{1'b1}};
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));
    `uvm_info(`gfn, $sformatf("FLASH OP PROGRAM START OP: %0p", flash_op), UVM_HIGH)
  endtask : do_cfg

  virtual task do_erase(flash_op_t flash_op_erase);
    flash_op_erase.op = FlashOpErase;
    flash_ctrl_start_op(flash_op_erase);
  endtask : do_erase

  virtual task do_prog(flash_op_t flash_op);
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));
    flash_ctrl_start_op(flash_op);
    flash_ctrl_write(flash_op_data, poll_fifo_status);
  endtask : do_prog

  virtual task do_read(flash_op_t flash_op_rd);
    poll_fifo_status = 0;
    cfg.flash_mem_bkdr_write(.flash_op(flash_op_rd), .scheme(FlashMemInitRandomize));
    flash_ctrl_start_op(flash_op_rd);
    flash_ctrl_read(flash_op_rd.num_words, flash_op_data, poll_fifo_status);
  endtask : do_read

  virtual task low_ready_h();
    cfg.flash_ctrl_vif.power_ready_h = 1'b0;
    cfg.clk_rst_vif.wait_clks(1);
    cfg.flash_ctrl_vif.power_ready_h = 1'b1;
  endtask : low_ready_h

endclass : flash_ctrl_mid_op_rst_vseq
