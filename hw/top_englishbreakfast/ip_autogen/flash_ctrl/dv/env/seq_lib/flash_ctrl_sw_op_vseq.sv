// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Pseudo Code
// Backdoor Write to FLASH (Initialize)
// FLASH Read - Compare Frontdoor
// FLASH Erase (Includes Backdoor Erase Check)
// FLASH Program
// FLASH Read - Compare Frontdoor

// Simple sw_op test
class flash_ctrl_sw_op_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_sw_op_vseq)

  // Class Members

  flash_op_t                                    flash_op;
  uint                                          bank;

  // Bit vector representing which of the mp region cfg CSRs to enable.
  bit           [flash_ctrl_pkg::MpRegions-1:0] en_mp_regions;

  // Indicates whether to poll before writing to the prog_fifo or reading from the rd_fifo. If interupts are
  // enabled, the interrupt signals will be used instead. When set to 0, it will continuously write
  // to prog_fifo / read from rd_fifo, relying on their natural backpressure mechanism.
  bit                                           poll_fifo_status;

  // Flash Data Queue
  rand data_q_t                                 flash_op_data;

  `uvm_object_new

  // Configure sequence knobs to tailor it to this seq.
  virtual function void configure_vseq();
    // Enable NO memory protection regions.
    cfg.seq_cfg.num_en_mp_regions   = 0;
    cfg.seq_cfg.poll_fifo_status_pc = 0;
    cfg.seq_cfg.check_mem_post_tran = 1;

    // Do Not enable access to any of the information partitions.
    foreach (cfg.seq_cfg.mp_info_page_en_pc[i, j]) begin
      cfg.seq_cfg.mp_info_page_en_pc[i][j] = 0;
    end
  endfunction

  // Body
  task body();

    logic                 [TL_DW-1:0] rdata;
    logic                 [TL_DW-1:0] exp_data [$];
    mubi4_t                           default_region_read_en;
    mubi4_t                           default_region_program_en;
    mubi4_t                           default_region_erase_en;

    // Configure the FLASH Controller

    // Memory protection regions settings. One MP region, Single Page
    flash_mp_region_cfg_t             mp_regions                [flash_ctrl_pkg::MpRegions];

    foreach (mp_regions[i]) begin
      mp_regions[i].en         = mubi4_bool_to_mubi(en_mp_regions[i]);
      mp_regions[i].read_en    = MuBi4True;
      mp_regions[i].program_en = MuBi4True;
      mp_regions[i].erase_en   = MuBi4True;
      mp_regions[i].start_page = MuBi4False;
      mp_regions[i].num_pages  = MuBi4True;
    end

    default_region_read_en    = MuBi4True;
    default_region_program_en = MuBi4True;
    default_region_erase_en   = MuBi4True;

    // Configure the flash based on the given settings
    foreach (mp_regions[i]) begin
      flash_ctrl_mp_region_cfg(i, mp_regions[i]);
    end

    flash_ctrl_default_region_cfg(.read_en(default_region_read_en),
                                  .program_en(default_region_program_en),
                                  .erase_en(default_region_erase_en));

    // TEST SETUP

    bank               = 0;  // Bank 0
    flash_op.addr      = 0;  // Start Address
    flash_op.partition = FlashPartData;  // Data Partition
    flash_op.num_words = 10;  // Number Of Words
    poll_fifo_status   = 0;  // FIFO Poll Status

    // INITIALIZE FLASH

    // Randomize Write Data
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(flash_op_data, flash_op_data.size == flash_op.num_words;)

    // Invalidate the flash mem contents. We do this because we operate on and check a specific
    // chunk of space. The rest of the flash mem is essentially dont-care. If the flash ctrl
    // does not work correctly, the check will result in an access from the invalidated mem
    // region exposing the issue.
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);

    `uvm_info(`gfn, $sformatf("Starting backdoor write operation with random values"), UVM_LOW)
    cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));

    // FLASH READ 1
    // Read Frontdoor, Compare Backdoor

    // Select FLASH Read Operation
    flash_op.op = flash_ctrl_pkg::FlashOpRead;

    // Start Controller
    flash_ctrl_start_op(flash_op);

    flash_ctrl_read(flash_op.num_words, flash_op_data, poll_fifo_status);
    wait_flash_op_done();
    if (cfg.seq_cfg.check_mem_post_tran) cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);

    // FLASH ERASE

    // Select FLASH Read Operation
    flash_op.op = flash_ctrl_pkg::FlashOpErase;

    // Select Page Erase
    flash_op.erase_type = flash_ctrl_pkg::FlashErasePage;

    // Start Controller
    flash_ctrl_start_op(flash_op);

    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
    if (cfg.seq_cfg.check_mem_post_tran) cfg.flash_mem_bkdr_erase_check(flash_op, exp_data);

    // FLASH PROGRAM
    // Write Frontdoor, Read backdoor

    // Select FLASH Operation
    flash_op.op = flash_ctrl_pkg::FlashOpProgram;

    // Randomize Write Data
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(flash_op_data, flash_op_data.size == flash_op.num_words;)

    // Calculate expected data for post-transaction checks
    exp_data = cfg.calculate_expected_data(flash_op, flash_op_data);

    // Start Controller
    flash_ctrl_start_op(flash_op);

    flash_ctrl_write(flash_op_data, poll_fifo_status);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
    if (cfg.seq_cfg.check_mem_post_tran) cfg.flash_mem_bkdr_read_check(flash_op, exp_data);

    // FLASH READ 2
    // Read Frontdoor, Compare Backdoor

    // Select FLASH Read Operation
    flash_op.op = flash_ctrl_pkg::FlashOpRead;

    // Start Controller
    flash_ctrl_start_op(flash_op);

    flash_ctrl_read(flash_op.num_words, flash_op_data, poll_fifo_status);
    wait_flash_op_done();
    if (cfg.seq_cfg.check_mem_post_tran) cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);

  endtask : body

endclass : flash_ctrl_sw_op_vseq
