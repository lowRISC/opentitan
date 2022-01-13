// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_base_vseq extends cip_base_vseq #(
  .RAL_T              (flash_ctrl_core_reg_block),
  .CFG_T              (flash_ctrl_env_cfg),
  .COV_T              (flash_ctrl_env_cov),
  .VIRTUAL_SEQUENCER_T(flash_ctrl_virtual_sequencer)
);
  `uvm_object_utils(flash_ctrl_base_vseq)

  // flash ctrl configuration settings.

  constraint num_trans_c {num_trans inside {[1 : cfg.seq_cfg.max_num_trans]};}

  `uvm_object_new

  // Determine post-reset initialization method.
  rand flash_mem_init_e flash_init;

  // default region cfg
  flash_mp_region_cfg_t default_region_cfg = '{default:1, scramble_en:0, ecc_en:0, he_en:0,
                                               num_pages:1, start_page:0};

  // default info cfg
  flash_bank_mp_info_page_cfg_t default_info_page_cfg = '{default:1, scramble_en:0, ecc_en:0,
                                                          he_en:0};

  // By default, in 30% of the times initialize flash as in initial state (all 1s),
  //  while in 70% of the times the initialization will be randomized (simulating working flash).
  constraint flash_init_c {
    flash_init dist {
      FlashMemInitSet       :/ cfg.seq_cfg.flash_init_set_pc,
      FlashMemInitRandomize :/ 100 - cfg.seq_cfg.flash_init_set_pc
    };
  }

  // Vseq to do some initial post-reset actions. Can be overriden by extending envs.
  flash_ctrl_callback_vseq callback_vseq;

  virtual task pre_start();
    `uvm_create_on(callback_vseq, p_sequencer);
    super.pre_start();
  endtask

  // After finishing basic dut_init do some additional required actions with callback_vseq
  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    callback_vseq.dut_init_callback();
  endtask : dut_init

  virtual task dut_shutdown();
    // check for pending flash_ctrl operations and wait for them to complete
    // TODO
  endtask

  virtual task reset_flash();
    // Set all flash partitions to 1s.
    flash_dv_part_e part = part.first();
    do begin
      cfg.flash_mem_bkdr_init(part, flash_init);
      part = part.next();
    end while (part != part.first());
    // Wait for flash_ctrl to finish initializing on every reset
    // We probably need a parameter to skip this for certain tests
    csr_spinwait(.ptr(ral.status.init_wip), .exp_data(1'b0));
  endtask : reset_flash

  virtual task apply_reset(string kind = "HARD");
    uvm_reg_data_t data;
    bit init_busy;
    super.apply_reset(kind);
    if (kind == "HARD") begin
      cfg.clk_rst_vif.wait_clks(cfg.post_reset_delay_clks);
    end
    reset_flash();

  endtask  // apply_reset

  // Configure the memory protection regions.
  virtual task flash_ctrl_mp_region_cfg(uint index, flash_mp_region_cfg_t region_cfg =
                                        default_region_cfg);
    uvm_reg_data_t data;
    uvm_reg csr;
    //verilog_format: off
    data =
        get_csr_val_with_updated_field(ral.mp_region_cfg_shadowed[index].en, data,
                                       region_cfg.en) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_shadowed[index].rd_en, data,
                                       region_cfg.read_en) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_shadowed[index].prog_en, data,
                                       region_cfg.program_en) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_shadowed[index].erase_en, data,
                                       region_cfg.erase_en) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_shadowed[index].scramble_en, data,
                                       region_cfg.scramble_en) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_shadowed[index].ecc_en, data,
                                       region_cfg.ecc_en) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_shadowed[index].he_en, data,
                                       region_cfg.he_en) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_shadowed[index].base, data,
                                       region_cfg.start_page) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_shadowed[index].size, data,
                                       region_cfg.num_pages);
    //verilog_format: on
    csr_wr(.ptr(ral.mp_region_cfg_shadowed[index]), .value(data));
  endtask

  // Configure the protection for the "default" region (all pages that do not fall into one
  // of the memory protection regions).
  virtual task flash_ctrl_default_region_cfg(bit read_en = 1, bit program_en = 1, bit erase_en = 1,
                                             bit scramble_en = 0, bit ecc_en = 0, bit he_en = 0);
    uvm_reg_data_t data;

    data = get_csr_val_with_updated_field(ral.default_region_shadowed.rd_en, data, read_en) |
        get_csr_val_with_updated_field(ral.default_region_shadowed.prog_en, data, program_en) |
        get_csr_val_with_updated_field(ral.default_region_shadowed.erase_en, data, erase_en) |
        get_csr_val_with_updated_field(ral.default_region_shadowed.scramble_en, data,
                                       scramble_en) |
        get_csr_val_with_updated_field(ral.default_region_shadowed.ecc_en, data, ecc_en) |
        get_csr_val_with_updated_field(ral.default_region_shadowed.he_en, data, he_en);
    csr_wr(.ptr(ral.default_region_shadowed), .value(data));
  endtask

  // Configure the memory protection of some selected page in one of the information partitions in
  //  one of the banks.
  virtual task flash_ctrl_mp_info_page_cfg(uint bank, uint info_part, uint page,
                                  flash_bank_mp_info_page_cfg_t page_cfg = default_info_page_cfg);
    uvm_reg_data_t data;
    uvm_reg csr;
    string csr_name = $sformatf("bank%0d_info%0d_page_cfg_shadowed", bank, info_part);
    // If the selected information partition has only 1 page, no suffix needed to the register
    //  name, if there is more than one page, the page index should be added to the register name.
    if (flash_ctrl_pkg::InfoTypeSize[info_part] > 1) begin
      csr_name = $sformatf({csr_name, "_%0d"}, page);
    end
    csr = ral.get_reg_by_name(csr_name);
    data = get_csr_val_with_updated_field(csr.get_field_by_name("en"), data, page_cfg.en) |
        get_csr_val_with_updated_field(csr.get_field_by_name("rd_en"), data, page_cfg.read_en) |
        get_csr_val_with_updated_field(csr.get_field_by_name("prog_en"), data,
                                       page_cfg.program_en) |
        get_csr_val_with_updated_field(csr.get_field_by_name("erase_en"), data,
                                       page_cfg.erase_en) |
        get_csr_val_with_updated_field(csr.get_field_by_name("scramble_en"), data,
                                       page_cfg.scramble_en) |
        get_csr_val_with_updated_field(csr.get_field_by_name("ecc_en"), data,
                                       page_cfg.ecc_en) |
        get_csr_val_with_updated_field(csr.get_field_by_name("he_en"), data,
                                       page_cfg.he_en);
    csr_wr(.ptr(csr), .value(data));
  endtask

  // Configure bank erasability.
  virtual task flash_ctrl_bank_erase_cfg(bit [flash_ctrl_pkg::NumBanks-1:0] bank_erase_en);
    csr_wr(.ptr(ral.mp_bank_cfg_shadowed[0]), .value(bank_erase_en));
  endtask

  // Configure read and program fifo levels for interrupt.
  virtual task flash_ctrl_fifo_levels_cfg_intr(uint read_fifo_intr_level,
                                               uint program_fifo_intr_level);
    uvm_reg_data_t data;

    data = get_csr_val_with_updated_field(ral.fifo_lvl.prog, data, program_fifo_intr_level) |
        get_csr_val_with_updated_field(ral.fifo_lvl.rd, data, read_fifo_intr_level);
    csr_wr(.ptr(ral.fifo_lvl), .value(data));
  endtask

  // Reset the program and read fifos.
  virtual task flash_ctrl_fifo_reset(bit reset = 1'b1);
    csr_wr(.ptr(ral.fifo_rst), .value(reset));
  endtask

  // Wait for flash_ctrl op to finish.
  virtual task wait_flash_op_done(
      bit clear_op_status = 1'b1, time timeout_ns = 10_000_000
  );  // Added because mass(bank) erase is longer then default timeout.
    uvm_reg_data_t data;
    bit done;
    `DV_SPINWAIT(do begin
        csr_rd(.ptr(ral.op_status), .value(data));
        done = get_field_val(ral.op_status.done, data);
      end while (done == 1'b0);, "wait_flash_op_done timeout occurred!", timeout_ns)
    if (clear_op_status) begin
      data = get_csr_val_with_updated_field(ral.op_status.done, data, 0);
      csr_wr(.ptr(ral.op_status), .value(data));
    end
  endtask

  // Wait for flash_ctrl op to finish with error.
  virtual task wait_flash_op_err(bit clear_op_status = 1'b1);
    uvm_reg_data_t data;
    bit err;
    `DV_SPINWAIT(do begin
        csr_rd(.ptr(ral.op_status), .value(data));
        err = get_field_val(ral.op_status.err, data);
      end while (err == 1'b0);, "wait_flash_op_err timeout occurred!")
    if (clear_op_status) begin
      data = get_csr_val_with_updated_field(ral.op_status.err, data, 0);
      csr_wr(.ptr(ral.op_status), .value(data));
    end
  endtask

  // Wait for prog fifo to not be full.
  virtual task wait_flash_ctrl_prog_fifo_not_full();
    // TODO: if intr enabled, then check interrupt, else check status.
    bit prog_full;
    `DV_SPINWAIT(do begin
        csr_rd(.ptr(ral.status.prog_full), .value(prog_full));
      end while (prog_full);, "wait_flash_ctrl_prog_fifo_not_full timeout occurred!")
  endtask

  // Wait for rd fifo to not be empty.
  virtual task wait_flash_ctrl_rd_fifo_not_empty();
    // TODO: if intr enabled, then check interrupt, else check status.
    bit read_empty;
    `DV_SPINWAIT(do begin
        csr_rd(.ptr(ral.status.rd_empty), .value(read_empty));
      end while (read_empty);, "wait_flash_ctrl_rd_fifo_not_empty timeout occurred!")
  endtask

  virtual task flash_ctrl_start_op(flash_op_t flash_op);
    uvm_reg_data_t data;
    flash_part_e partition_sel;
    bit [InfoTypesWidth-1:0] info_sel;


    csr_wr(.ptr(ral.addr), .value(flash_op.addr));

    //    flash_op.partition     -> partition_sel  ,    info_sel         |
    //     (flash_dv_part_e)     | (flash_part_e)  | bit[InfoTypesWidth] |
    // --------------------------|-----------------|---------------------|
    //  FlashPartData        = 0 | FlashPartData=0 |         0           |
    //  FlashPartInfo        = 1 | FlashPartInfo=1 |         0           |
    //  FlashPartInfo1       = 2 | FlashPartInfo=1 |         1           |
    //  FlashPartRedundancy  = 4 | FlashPartInfo=1 |         2           |
    partition_sel = |flash_op.partition;
    info_sel = flash_op.partition >> 1;

    data = get_csr_val_with_updated_field(ral.control.start, data, 1'b1) |
        get_csr_val_with_updated_field(ral.control.op, data, flash_op.op) |
        get_csr_val_with_updated_field(ral.control.erase_sel, data, flash_op.erase_type) |
        get_csr_val_with_updated_field(ral.control.partition_sel, data, partition_sel) |
        get_csr_val_with_updated_field(ral.control.info_sel, data, info_sel) |
        get_csr_val_with_updated_field(ral.control.num, data, flash_op.num_words - 1);
    csr_wr(.ptr(ral.control), .value(data));
  endtask

  // Program data into flash, stopping whenever full.
  // The flash op is assumed to have already commenced.
  virtual task flash_ctrl_write(data_q_t data, bit poll_fifo_status);
    foreach (data[i]) begin
      // Check if prog fifo is full. If yes, then wait for space to become available.
      // Note that this polling is not needed since the interface is backpressure enabled.
      if (poll_fifo_status) begin
        wait_flash_ctrl_prog_fifo_not_full();
      end
      mem_wr(.ptr(ral.prog_fifo), .offset(0), .data(data[i]));
      `uvm_info(`gfn, $sformatf("flash_ctrl_write: 0x%0h", data[i]), UVM_MEDIUM)
    end
  endtask

  // Read data from flash, stopping whenever empty.
  // The flash op is assumed to have already commenced.
  virtual task flash_ctrl_read(uint num_words, ref data_q_t data, bit poll_fifo_status);
    for (int i = 0; i < num_words; i++) begin
      // Check if rd fifo is empty. If yes, then wait for data to become available.
      // Note that this polling is not needed since the interface is backpressure enabled.
      if (poll_fifo_status) begin
        wait_flash_ctrl_rd_fifo_not_empty();
      end
      mem_rd(.ptr(ral.rd_fifo), .offset(0), .data(data[i]));
      `uvm_info(`gfn, $sformatf("flash_ctrl_read: 0x%0h", data[i]), UVM_MEDIUM)
    end
  endtask

  // Task to perform a direct Flash read at the specified location
  virtual task do_direct_read(
      input bit [TL_AW-1:0] addr, input bit [TL_DBW-1:0] mask = get_rand_contiguous_mask(),
      input bit blocking = $urandom_range(0, 1), input bit check_rdata = 0,
      input bit [TL_DW-1:0] exp_rdata = '0, input mubi4_t instr_type = MuBi4False,
      output logic [TL_DW-1:0] rdata);
    tl_access(.addr(addr), .write(1'b0), .data(rdata), .mask(mask), .blocking(blocking),
              .check_exp_data(check_rdata), .exp_data(exp_rdata), .compare_mask(mask),
              .instr_type(instr_type),
              .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.flash_ral_name]));
  endtask

endclass : flash_ctrl_base_vseq
