// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is base class for on the fly mode test sequence.
// On the fly mode test checks data integrity per transaction (program or read),
// and doesn't rely on reference memory model in the test bench.
class flash_ctrl_otf_base_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_otf_base_vseq)
  `uvm_object_new

  // Used for tracing programmed data
  bit[15:0] global_pat_cnt = 0;

  // Determine post-reset initialization method.
  flash_mem_init_e otf_flash_init = FlashMemInitSet;

  virtual task pre_start();
    configure_otf_mode(otf_flash_init);
    super.pre_start();
  endtask

  // On the fly scoreboard mode
  // This will disable reference memory check in the end of the test
  // as well as all intermediate transaction update for memory model.
  function void configure_otf_mode(flash_mem_init_e f_init = "FlashMemInitSet");
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::On;
    cfg.seq_cfg.en_init_keys_seeds = 1;
    cfg.scb_check                               = 0;
    cfg.check_full_scb_mem_model                = 0;
    cfg.scb_otf_en = 1;
  endfunction

  // Program flash in the unit of minimum resolution (8 words).
  // 1 word : 8Byte
  // @arg: flash_op_p : command struct return updated address after write
  // @arg: bank: band index to access flash
  // @arg: num : number of 8 words range: [1 : 32]
  // @arg: wd  : number of 4byte (TL bus unit) : default : 16
  task prog_flash(ref flash_op_t flash_op, input int bank, int num, int wd = 16);
    data_q_t flash_data_chunk;
    flash_otf_item exp_item;
    bit poll_fifo_status = 1;
    bit [15:0] lcnt = 0;
    bit [flash_ctrl_pkg::BusAddrW-1:0] start_addr, end_addr;

    flash_op.op = flash_ctrl_pkg::FlashOpProgram;
    flash_op.num_words = wd;
    start_addr = flash_op.otf_addr;
    end_addr = start_addr + (4 * wd) * num;
    // Check if end_addr overflows.
    // Roll over start address if this is the case.
    `uvm_info(`gfn, $sformatf("prog_flash: otf_addr:0x%0h, size:%0d x %0d x 4B",
                              flash_op.otf_addr, num, wd), UVM_MEDIUM)

    if (end_addr[flash_ctrl_pkg::BusAddrW-1]) begin
      start_addr = num * 64;
      flash_op.otf_addr = start_addr;
      `uvm_info(`gfn, $sformatf("prog_flash: overflow!, roll over start address to 0x%x",
                                start_addr), UVM_MEDIUM)
    end

    for (int i = 0; i < num; i++) begin
      // Each flash_program_data[] entry : 4B
      // {global_cnt(16bits), lcnt(16bits)}
      for (int j = 0; j < wd; j++) begin
        flash_program_data[j] = {global_pat_cnt, lcnt++};
        flash_data_chunk.push_back(flash_program_data[j]);
      end

      flash_op.addr = flash_op.otf_addr;
      flash_ctrl_start_op(flash_op);
      flash_ctrl_write(flash_program_data, poll_fifo_status);
      wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
      flash_op.otf_addr = flash_op.otf_addr + (4 * wd);

    end // for (int i = 0; i < num; i++)
    flash_otf_print_data64(flash_data_chunk, "wdata");
    `uvm_create_obj(flash_otf_item, exp_item)
    exp_item.cmd = flash_op;
    exp_item.dq = flash_data_chunk;

    // scramble data
    exp_item.scramble(otp_addr_key, otp_data_key, start_addr);

    p_sequencer.eg_exp_port[bank].write(exp_item);
    flash_phy_prim_agent_pkg::print_flash_data(exp_item.fq,
                                               $sformatf("fdata_%0d", cfg.otf_ctrl_wr_sent));
    global_pat_cnt++;
    cfg.otf_ctrl_wr_sent++;
  endtask // prog_flash

  // Read flash in the unit of minimum resolution (8 words).
  // 1 word : 8Byte
  // @arg: flash_op_p : command struct return updated address after write
  // @arg: bank: band index to access flash
  // @arg: num : number of 8 words range: [1 : 32]
  // @arg: wd  : number of 4byte (TL bus unit) : default : 16

  task read_flash(ref flash_op_t flash_op, input int bank, int num, int wd = 16);
    data_q_t flash_read_data, flash_data_chunk;
    flash_otf_item exp_item;
    bit poll_fifo_status = 1;
    bit [flash_ctrl_pkg::BusAddrW-1:0] start_addr, end_addr;

    flash_op.op = flash_ctrl_pkg::FlashOpRead;
    flash_op.num_words = wd;
    start_addr = flash_op.otf_addr;
    end_addr = start_addr + (4 * wd) * num;
    // Check if end_addr overflows.
    // Roll over start address if this is the case.
    `uvm_info(`gfn, $sformatf("read_flash: otf_addr:0x%0h, size:%0d x %0d",
                              flash_op.otf_addr, wd, num), UVM_MEDIUM)

    if (end_addr[flash_ctrl_pkg::BusAddrW-1]) begin
      start_addr = num * 64;
      flash_op.otf_addr = start_addr;
      `uvm_info(`gfn, $sformatf("read_flash: overflow!, roll over start address to 0x%x",
                                start_addr), UVM_MEDIUM)
    end


    for (int i = 0; i < num; i++) begin
      flash_op.addr = flash_op.otf_addr;
      flash_ctrl_start_op(flash_op);
      flash_ctrl_read(flash_op.num_words, flash_read_data, poll_fifo_status);
      wait_flash_op_done();
      flash_op.otf_addr = flash_op.otf_addr + (4 * wd);
      foreach(flash_read_data[i]) flash_data_chunk.push_back(flash_read_data[i]);
    end // for (int i = 0; i < num; i++)

    flash_otf_print_data64(flash_data_chunk, "rdata");
    `uvm_create_obj(flash_otf_item, exp_item)
    exp_item.cmd = flash_op;
    exp_item.dq = flash_data_chunk;
    p_sequencer.eg_exp_port[bank].write(exp_item);

  endtask // read_flash
endclass // flash_ctrl_otf_base_vseq
