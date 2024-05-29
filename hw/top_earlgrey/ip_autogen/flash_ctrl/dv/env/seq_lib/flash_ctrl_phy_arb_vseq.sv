// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Flash Physical Controller Arbitration between host reads and controller operations
// 1.Scenario tests on the different banks arbitration
// 2.Scenario tests on the same bank arbitration
// 3.Scenario tests lost of priority of host read on the same bank
class flash_ctrl_phy_arb_vseq extends flash_ctrl_fetch_code_vseq;
  `uvm_object_utils(flash_ctrl_phy_arb_vseq)

  `uvm_object_new

  // Randomized flash ctrl operation.
  rand flash_op_t flash_op_host_rd;
  data_q_t flash_rd_data;

  rand uint bank_rd;

  // knob for testing arbitration on same or different banks
  logic bank_same = 0;

  // Constraint for banks.
  constraint bank_c {
    solve bank before bank_rd;
    if (bank_same == 1) {bank == bank_rd;} else {bank != bank_rd;}
    bank inside {[0 : flash_ctrl_pkg::NumBanks - 1]};
    bank_rd inside {[0 : flash_ctrl_pkg::NumBanks - 1]};
  }

  // Constraint host read address to be in relevant range for the selected partition.
  constraint addr_rd_c {
    solve bank_rd before flash_op_host_rd;
    flash_op_host_rd.addr inside {[BytesPerBank * bank_rd :
                                   BytesPerBank * (bank_rd + 1) - BytesPerBank / 2]};
  }

  constraint flash_op_host_rd_c {
    flash_op_host_rd.partition == FlashPartData;
    flash_op_host_rd.num_words inside {[10 : FlashNumBusWords -
                                        flash_op_host_rd.addr[TL_AW-1:TL_SZW]]};
    flash_op_host_rd.num_words <= cfg.seq_cfg.op_max_words;
    flash_op_host_rd.num_words < FlashPgmRes - flash_op_host_rd.addr[TL_SZW+:FlashPgmResWidth];
  }


  addr_t read_addr;

  // Single direct read data
  data_t flash_rd_one_data;

  localparam data_t AllOnes = {TL_DW{1'b1}};

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();
    // MAx number of transactions.
    cfg.seq_cfg.max_num_trans           = 10;

    super.configure_vseq();
  endfunction

  virtual task body();

    // enable sw rw access
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::On;

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
      end else if (flash_op.op == flash_ctrl_pkg::FlashOpRead) begin
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
      end else if (flash_op.op == flash_ctrl_pkg::FlashOpRead) begin
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
        host_read_data(flash_op_host_rd);
      end
      begin
        // controller read, program or erase
        if (flash_op.op == flash_ctrl_pkg::FlashOpRead) begin
          controller_read_data(flash_op);
        end else if (flash_op.op == flash_ctrl_pkg::FlashOpProgram) begin
          controller_program_data(flash_op, flash_op_data);
        end else begin  //flash_op.op == flash_ctrl_pkg::FlashOpErase
          controller_erase_data(flash_op);
        end
      end
    join;
  endtask : do_operations

  // host read data.
  virtual task host_read_data(flash_op_t flash_op);
    data_4s_t rdata;
    bit comp;
    for (int j = 0; j < flash_op.num_words; j++) begin
      read_addr = flash_op.addr + 4 * j;
      do_direct_read(.addr(read_addr), .mask('1), .blocking(cfg.block_host_rd), .check_rdata(0),
                     .rdata(rdata), .completed(comp));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
    end
  endtask : host_read_data

  // Controller read data.
  virtual task controller_read_data(flash_op_t flash_op);
    flash_rd_data.delete();
    flash_ctrl_start_op(flash_op);
    flash_ctrl_read(flash_op.num_words, flash_rd_data, poll_fifo_status);
    wait_flash_op_done();
    `uvm_info(`gfn, $sformatf("FLASH OP READ DATA: %0p", flash_rd_data), UVM_HIGH)
    cfg.flash_mem_bkdr_read_check(flash_op, flash_rd_data);
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
  endtask : controller_read_data

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
  virtual task controller_erase_data(flash_op_t flash_op);
    data_q_t exp_data;
    exp_data = cfg.calculate_expected_data(flash_op, flash_op_data);
    flash_ctrl_start_op(flash_op);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
    `uvm_info(`gfn, $sformatf("FLASH OP ERASE DATA DONE"), UVM_HIGH)
    cfg.flash_mem_bkdr_erase_check(flash_op, exp_data);
  endtask : controller_erase_data

  virtual task do_arb();
    data_4s_t rdata;
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
        bit comp;
        `uvm_info(`gfn, $sformatf("FLASH OP HOST RD ARB: %0p", flash_op_host_rd), UVM_HIGH)
        cfg.clk_rst_vif.wait_clks(32);
        for (int j = 0; j < flash_op_host_rd.num_words; j++) begin
          read_addr = flash_op_host_rd.addr + 4 * j;
          do_direct_read(.addr(read_addr), .mask('1), .blocking(cfg.block_host_rd),
                         .check_rdata(0), .rdata(rdata), .completed(comp));
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
        `DV_CHECK_EQ(flash_rd_one_data, AllOnes)
      end
      if (j == 5) begin
        `DV_CHECK_EQ(flash_rd_one_data, flash_op_data[0])
      end
    end

  endtask : do_arb

endclass : flash_ctrl_phy_arb_vseq
