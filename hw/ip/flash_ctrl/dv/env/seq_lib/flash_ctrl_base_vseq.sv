// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (flash_ctrl_reg_block),
    .CFG_T               (flash_ctrl_env_cfg),
    .COV_T               (flash_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (flash_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(flash_ctrl_base_vseq)

  // flash ctrl configuration settings.

  constraint num_trans_c {
    num_trans inside {[1:cfg.seq_cfg.max_num_trans]};
  }

  `uvm_object_new

  virtual task dut_shutdown();
    // check for pending flash_ctrl operations and wait for them to complete
    // TODO
  endtask

  virtual task apply_reset(string kind = "HARD");
    uvm_reg_data_t data;
    bit init_busy;
    super.apply_reset(kind);
    if (kind == "HARD") begin
      cfg.clk_rst_vif.wait_clks(cfg.post_reset_delay_clks);
    end
    cfg.flash_mem_bkdr_init(FlashPartInfo1, FlashMemInitSet);

    // Wait for flash_ctrl to finish initializing on every reset
    // We probably need a parameter to skip this for certain tests
    csr_spinwait(.ptr(ral.status.init_wip), .exp_data(1'b0));

  endtask // apply_reset

  // Configure the memory protection regions.
  virtual task flash_ctrl_mp_region_cfg(uint index, flash_mp_region_cfg_t region_cfg);
    uvm_reg_data_t data;
    uvm_reg csr;
    data =
        get_csr_val_with_updated_field(ral.mp_region_cfg_0.en_0, data, region_cfg.en) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_0.rd_en_0, data, region_cfg.read_en) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_0.prog_en_0, data, region_cfg.program_en) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_0.erase_en_0, data, region_cfg.erase_en) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_0.base_0, data, region_cfg.start_page) |
        get_csr_val_with_updated_field(ral.mp_region_cfg_0.size_0, data, region_cfg.num_pages);
    csr = ral.get_reg_by_name($sformatf("mp_region_cfg_%0d", index));
    csr_wr(.csr(csr), .value(data));
  endtask

  // Configure the protection for the "default" region (all pages that do not fall into one
  // of the memory protection regions).
  virtual task flash_ctrl_default_region_cfg(bit read_en, bit program_en, bit erase_en);
    uvm_reg_data_t data;

    data = get_csr_val_with_updated_field(ral.default_region.rd_en, data, read_en) |
           get_csr_val_with_updated_field(ral.default_region.prog_en, data, program_en) |
           get_csr_val_with_updated_field(ral.default_region.erase_en, data, erase_en);
    csr_wr(.csr(ral.default_region), .value(data));
  endtask

  // Configure bank erasability.
  virtual task flash_ctrl_bank_erase_cfg(bit [flash_ctrl_pkg::NumBanks-1:0] bank_erase_en);
    csr_wr(.csr(ral.mp_bank_cfg), .value(bank_erase_en));
  endtask

  // Configure read and program fifo levels for interrupt.
  virtual task flash_ctrl_fifo_levels_cfg_intr(uint read_fifo_intr_level,
                                               uint program_fifo_intr_level);
    uvm_reg_data_t data;

    data = get_csr_val_with_updated_field(ral.fifo_lvl.prog, data, program_fifo_intr_level) |
           get_csr_val_with_updated_field(ral.fifo_lvl.rd, data, read_fifo_intr_level);
    csr_wr(.csr(ral.fifo_lvl), .value(data));
  endtask

  // Reset the program and read fifos.
  virtual task flash_ctrl_fifo_reset(bit reset = 1'b1);
    csr_wr(.csr(ral.fifo_rst), .value(reset));
  endtask

  // Wait for flash_ctrl op to finish.
  virtual task wait_flash_op_done(bit clear_op_status = 1'b1,
                                 time timeout_ns = 10_000_000); // Added because mass(bank) erase is longer then default timeout.
    uvm_reg_data_t data;
    bit done;
    `DV_SPINWAIT(
      do begin
        csr_rd(.ptr(ral.op_status), .value(data));
        done = get_field_val(ral.op_status.done, data);
      end while (done == 1'b0);,
      "wait_flash_op_done timeout occurred!",
      timeout_ns
    )
    if (clear_op_status) begin
      data = get_csr_val_with_updated_field(ral.op_status.done, data, 0);
      csr_wr(.csr(ral.op_status), .value(data));
    end
  endtask

  // Wait for flash_ctrl op to finish with error.
  virtual task wait_flash_op_err(bit clear_op_status = 1'b1);
    uvm_reg_data_t data;
    bit err;
    `DV_SPINWAIT(
      do begin
        csr_rd(.ptr(ral.op_status), .value(data));
        err = get_field_val(ral.op_status.err, data);
      end while (err == 1'b0);,
      "wait_flash_op_err timeout occurred!"
    )
    if (clear_op_status) begin
      data = get_csr_val_with_updated_field(ral.op_status.err, data, 0);
      csr_wr(.csr(ral.op_status), .value(data));
    end
  endtask

  // Wait for prog fifo to not be full.
  virtual task wait_flash_ctrl_prog_fifo_not_full();
    // TODO: if intr enabled, then check interrupt, else check status.
    bit prog_full;
    `DV_SPINWAIT(
      do begin
        csr_rd(.ptr(ral.status.prog_full), .value(prog_full));
      end while (prog_full);,
      "wait_flash_ctrl_prog_fifo_not_full timeout occurred!"
    )
  endtask

  // Wait for rd fifo to not be empty.
  virtual task wait_flash_ctrl_rd_fifo_not_empty();
    // TODO: if intr enabled, then check interrupt, else check status.
    bit read_empty;
    `DV_SPINWAIT(
      do begin
        csr_rd(.ptr(ral.status.rd_empty), .value(read_empty));
      end while (read_empty);,
      "wait_flash_ctrl_rd_fifo_not_empty timeout occurred!"
    )
  endtask

  virtual task flash_ctrl_start_op(flash_op_t flash_op);
    uvm_reg_data_t data;
    flash_part_e partition_sel;
    bit [InfoTypesWidth-1:0] info_sel;


    csr_wr(.csr(ral.addr), .value(flash_op.addr));

    // flash_op.partition -> partition_sel  ,    info_sel         |
    //  (flash_dv_part_e) | (flash_part_e)  | bit[InfoTypesWidth] |
    // -------------------|-----------------|---------------------|
    //  FlashPartData = 0 | FlashPartData=0 |         0           |
    //  FlashPartInfo = 1 | FlashPartInfo=1 |         0           |
    //  FlashPartInfo1= 2 | FlashPartInfo=1 |         1           |
    //  FlashPartRed  = 4 | FlashPartInfo=1 |         2           |
    partition_sel = |flash_op.partition;
    info_sel = flash_op.partition >> 1;

    data =
        get_csr_val_with_updated_field(ral.control.start, data, 1'b1) |
        get_csr_val_with_updated_field(ral.control.op, data, flash_op.op) |
        get_csr_val_with_updated_field(ral.control.erase_sel, data, flash_op.erase_type) |
        get_csr_val_with_updated_field(ral.control.partition_sel, data, partition_sel) |
        get_csr_val_with_updated_field(ral.control.info_sel, data, info_sel) |
        get_csr_val_with_updated_field(ral.control.num, data, flash_op.num_words - 1);
    csr_wr(.csr(ral.control), .value(data));
  endtask

  // Program data into flash, stopping whenever full.
  // The flash op is assumed to have already commenced.
  virtual task flash_ctrl_write(bit [TL_DW-1:0] data[$], bit poll_fifo_status);
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
  virtual task flash_ctrl_read(uint num_words, ref bit [TL_DW-1:0] data[$], bit poll_fifo_status);
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


endclass : flash_ctrl_base_vseq
