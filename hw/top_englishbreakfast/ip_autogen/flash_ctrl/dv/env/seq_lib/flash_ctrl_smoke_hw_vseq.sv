// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke hardware interface test for direct reading
class flash_ctrl_smoke_hw_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_smoke_hw_vseq)

  `uvm_object_new

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();
    // Enable one memory protection region.
    cfg.seq_cfg.num_en_mp_regions = 1;

    // Don't enable access to any of information partitions.
    foreach (cfg.seq_cfg.mp_info_page_en_pc[i, j]) begin
      cfg.seq_cfg.mp_info_page_en_pc[i][j] = 0;
    end
  endfunction

  task body();
    data_4s_t rdata;
    data_q_t exp_data;

    int flash_depth = flash_ctrl_reg_pkg::BytesPerBank / 4;

    mubi4_t default_region_read_en;
    mubi4_t default_region_program_en;
    mubi4_t default_region_erase_en;

    // Bank 0 is used
    uint bank;

    // A single PROGRAM flash ctrl operation.
    flash_op_t flash_op;

    // Bit vector representing which of the mp region cfg CSRs to enable.
    bit [flash_ctrl_pkg::MpRegions-1:0] en_mp_regions;

    // Memory protection regions settings. One MP region, Single Page
    flash_mp_region_cfg_t mp_region;
    bit                                 comp;

    default_region_read_en    = MuBi4True;
    default_region_program_en = MuBi4True;
    default_region_erase_en   = MuBi4True;

    bank = 0;

    flash_op.addr = 0;
    flash_op.op = flash_ctrl_pkg::FlashOpProgram;
    flash_op.partition = FlashPartData;
    flash_op.num_words = 10;

    en_mp_regions = cfg.seq_cfg.num_en_mp_regions;

    mp_region.en = mubi4_bool_to_mubi(en_mp_regions);
    mp_region.read_en = MuBi4True;
    mp_region.program_en = MuBi4True;
    mp_region.erase_en = MuBi4True;
    mp_region.start_page = 0;
    mp_region.num_pages = 1;

    `uvm_info(`gfn, $sformatf("Configuring flash_ctrl, flash_depth %0d", flash_depth), UVM_MEDIUM)

    // If external_cfg=1 it means this sequence is being randomized by another sequence and this
    //  randomization will possibly override the upper randomization (Added specifically for
    //  partner sequences using this one).
    if (!cfg.seq_cfg.external_cfg) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
    end

    // Configure the flash based on the settings.
    flash_ctrl_mp_region_cfg(0, mp_region);

    flash_ctrl_default_region_cfg(.read_en(default_region_read_en),
                                  .program_en(default_region_program_en),
                                  .erase_en(default_region_erase_en));

    // Invalidate the flash mem contents. We do this because we operate on and check a specific
    // chunk of space. The rest of the flash mem is essentially dont-care. If the flash ctrl
    // does not work correctly, the check will result in an access from the invalidated mem
    // region exposing the issue.
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);

    `uvm_info(`gfn, $sformatf("Starting backdoor write operation with random values"), UVM_HIGH)
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));

    // Host direct read of random written value
    `uvm_info(`gfn, $sformatf("Starting direct read"), UVM_HIGH)
    for (int j = 0; j < 10; j++) begin
      do_direct_read(.addr(j * 4), .mask('1), .blocking(1), .check_rdata(0), .rdata(rdata),
                     .completed(comp));
      exp_data.push_back(rdata);
    end

    // Backdoor read of random written values and comparing with previously read values
    `uvm_info(`gfn, $sformatf("Starting backdoor read for checking data"), UVM_HIGH)
    cfg.flash_mem_bkdr_read_check(flash_op, exp_data);

  endtask : body

endclass : flash_ctrl_smoke_hw_vseq
