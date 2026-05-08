// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// flash_ctrl_basic_rw

// This test does the following in a loop:
// 0. randomize scramble_en, ecc_en, data, address
// 1. initialize flash with all ones
// 2. program flash with random data
// 3. read back data through host interface
// 4. read back data through controller interface

class flash_ctrl_basic_rw_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_basic_rw_vseq)

  `uvm_object_new

  // Class Members
  rand data_q_t flash_op_data;
  rand flash_op_t flash_op;
  rand uint bank;
  rand mubi4_t instr_type;
  rand uint num_trans;
  rand mubi4_t scramble_en, ecc_en;

  constraint bank_c {bank inside {[0 : flash_ctrl_top_specific_pkg::NumBanks - 1]};}
  constraint scramble_c {scramble_en inside {MuBi4True, MuBi4False};}
  constraint ecc_c {ecc_en inside {MuBi4True, MuBi4False};}

  constraint num_trans_c {num_trans < 100;}

  // Constraint for controller address to be in relevant range for the selected partition.
  constraint addr_c {
    solve bank before flash_op.addr;
    flash_op.addr inside {[BytesPerBank * bank : BytesPerBank * (bank + 1)]};
    flash_op.addr[2:0] == '0;
  }

  constraint flash_op_c {
    // Bank Erase is only supported for Data & 1st Info Partitions
    flash_op.partition == FlashPartData;

    flash_op.op inside {flash_ctrl_top_specific_pkg::FlashOpProgram,
                        flash_ctrl_top_specific_pkg::FlashOpRead};

    flash_op.num_words >= 10;
    flash_op.num_words <= (FlashNumBusWords - flash_op.addr[TL_AW-1:TL_SZW]);
    flash_op.num_words <= 256;
    flash_op.num_words < (FlashPgmRes - flash_op.addr[TL_SZW+:FlashPgmResWidth]);
  }

  // Flash ctrl operation data queue - used for programming or reading the flash.
  constraint flash_op_data_c {
    solve flash_op.num_words before flash_op_data;

    flash_op_data.size() == flash_op.num_words;
  }

  // Body
  virtual task body();

    // Local Variables
    addr_t read_addr;
    data_t rdata;
    bit comp, exp_err;
    data_q_t flash_op_rdata;

    // Scoreboard knob for Blocking Read Data Checking
    // Checks performed in this test
    cfg.block_host_rd = 0;

    // enable code execution
    csr_wr(.ptr(ral.exec), .value(CODE_EXEC_KEY));

    // Enable All Regions

    // disable randomization for num_trans (loop variable)
    num_trans.rand_mode(0);

    for (int k = 0; k < num_trans; k++) begin

      // re-randomize all variables
      randomize();

      // 0. initialize regions
      init_flash_regions(scramble_en, ecc_en);

      // 1. init flash memory to all ones
      cfg.flash_mem_bkdr_init(FlashPartData, FlashMemInitSet);

      // 2. program random data to flash
      for (int i = 0; i < flash_op.num_words; i++) begin
        `uvm_info(`gfn, $sformatf("DATA %p", flash_op_data[i]), UVM_HIGH)
      end
      flash_op.op = flash_ctrl_top_specific_pkg::FlashOpProgram;
      flash_ctrl_base_vseq::flash_ctrl_write_extra(flash_op, flash_op_data, 1,
                                                   mubi4_test_true_strict(scramble_en),
                                                   mubi4_test_true_strict(ecc_en));

      exp_err = 0;

      // 3. Read from memory interface (direct read)
      for (int i = 0; i < flash_op.num_words; i++) begin
        read_addr = flash_op.addr + 4 * i;
        instr_type = get_rand_mubi4_val(.t_weight(2),
                                        .f_weight(2),
                                        .other_weight(0));


        do_direct_read(.addr(read_addr), .mask('1), .blocking(cfg.block_host_rd), .check_rdata(1),
                       .instr_type(instr_type), .rdata(rdata), .exp_rdata(flash_op_data[i]),
                       .exp_err_rsp(exp_err), .completed(comp));
        cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
      end
      csr_utils_pkg::wait_no_outstanding_access();

      // 4. Read from controller interface
      flash_op.op = flash_ctrl_top_specific_pkg::FlashOpRead;
      flash_ctrl_read_extra(flash_op, flash_op_rdata);
      for (int i = 0; i < flash_op.num_words; i++) begin
        if (flash_op_data[i] !== flash_op_rdata[i])
          `uvm_error("rd-err", $sformatf("Read-back error: exp: %x is: %x", flash_op_data[i],
                    flash_op_rdata[i]))
      csr_utils_pkg::wait_no_outstanding_access();
      end
    end

  endtask : body

  // Task to initialize the Flash Access
  virtual task init_flash_regions(mubi4_t scramble_en, mubi4_t ecc_en);

    // Memory Protection Regions
    flash_mp_region_cfg_t mp_regions[flash_ctrl_top_specific_pkg::MpRegions];

    for (int i = 0; i<flash_ctrl_top_specific_pkg::MpRegions; i++) begin
      mp_regions[i].en = MuBi4False;
      mp_regions[i].read_en = MuBi4True;
      mp_regions[i].program_en = MuBi4True;
      mp_regions[i].erase_en = MuBi4True;
      mp_regions[i].scramble_en = scramble_en;
      mp_regions[i].ecc_en = ecc_en;
      mp_regions[i].he_en = MuBi4False;
      mp_regions[i].start_page = 0;
      mp_regions[i].num_pages = FlashNumPages;
    end
    mp_regions[0].en = MuBi4True;

    // Initialize MP Regions
    foreach (mp_regions[k]) begin
      flash_ctrl_mp_region_cfg(k, mp_regions[k]);
      `uvm_info(`gfn, $sformatf("MP regions values %p", mp_regions[k]), UVM_HIGH)
    end

    // Initialize Default Regions
    flash_ctrl_default_region_cfg(
        .read_en(MuBi4True), .program_en(MuBi4True),
        .erase_en(MuBi4True), .scramble_en(scramble_en),
        .ecc_en(ecc_en), .he_en(MuBi4False));

  endtask : init_flash_regions

endclass : flash_ctrl_basic_rw_vseq
