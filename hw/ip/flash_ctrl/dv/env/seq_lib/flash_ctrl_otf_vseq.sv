// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is base class for on the fly mode test sequence.
// On the fly mode test checks data integrity per transaction (program or read),
// and doesn't rely on reference memory model in the test bench.
class flash_ctrl_otf_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_otf_vseq)
  `uvm_object_new

  // Used for tracing programmed data
  bit[15:0] global_pat_cnt = 0;

  virtual task pre_start();
    // Erased page doesn't go through descramble.
    // To maintain high stress rate,
    // keep flash_init to FlashMemInitRandomize
    flash_init_c.constraint_mode(0);
    flash_init = FlashMemInitRandomize;
    configure_otf_mode();
    super.pre_start();
    if (cfg.seq_cfg.en_init_keys_seeds == 1) begin
      while (otp_key_init_done != 2'b11) cfg.clk_rst_vif.wait_clks(1);
    end

    `JDBG(("flash init scheme: %s", flash_init.name()))
//    flash_ctrl_default_region_cfg(,,,MuBi4True); // ,,,MuBi4True
     flash_ctrl_default_region_cfg();


    // Polling init wip is done
    csr_spinwait(.ptr(ral.status.init_wip), .exp_data(1'b0));

    cfg.m_fpp_agent_cfg.mon_start = 1;

  endtask

  // On the fly scoreboard mode
  // This will disable reference memory check in the end of the test
  // as well as all intermediate transaction update for memory model.
  function void configure_otf_mode();
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::On;
    cfg.seq_cfg.en_init_keys_seeds = 1;
    cfg.scb_check                               = 0;
    cfg.check_full_scb_mem_model                = 0;
    cfg.scb_otf_en = 1;

    foreach (cfg.m_tl_agent_cfgs[i]) begin
      cfg.m_tl_agent_cfgs[i].a_valid_delay_min = 0;
      cfg.m_tl_agent_cfgs[i].a_valid_delay_max = 0;
      cfg.m_tl_agent_cfgs[i].d_valid_delay_min = 0;
      cfg.m_tl_agent_cfgs[i].d_valid_delay_max = 0;
      cfg.m_tl_agent_cfgs[i].a_ready_delay_min = 0;
      cfg.m_tl_agent_cfgs[i].a_ready_delay_max = 0;
      cfg.m_tl_agent_cfgs[i].d_ready_delay_min = 0;
      cfg.m_tl_agent_cfgs[i].d_ready_delay_max = 0;
    end
  endfunction

  // Program flash in the unit of minimum resolution (4Byte)
  // If data is not aligned to 8Byte, rtl pads all F to
  // upper or lower 4Byte.
  // @arg: flash_op_p : command struct return updated address after write
  // @arg: bank: bank index to access flash
  // @arg: num : number of 8 words range: [1 : 32]
  // @arg: wd  : number of 4byte (TL bus unit) : default : 16
  task prog_flash(ref flash_op_t flash_op, input int bank, int num, int wd = 16);
    data_q_t flash_data_chunk;
    flash_otf_item exp_item;
    bit poll_fifo_status = 1;
    bit [15:0] lcnt = 0;
    bit [flash_ctrl_pkg::BusAddrByteW-1:0] start_addr, end_addr;
    // If program address is not aligned to 8byte,
    bit is_odd;

    flash_op.op = flash_ctrl_pkg::FlashOpProgram;
    flash_op.num_words = wd;
    start_addr = flash_op.otf_addr;
    end_addr = start_addr + (4 * wd) * num;
    // Check if end_addr overflows.
    // Roll over start address if this is the case.
    `uvm_info(`gfn, $sformatf("prog_flash: bank:%0d otf_addr:0x%0h, size:%0d x %0d x 4B",
                              bank, flash_op.otf_addr, num, wd), UVM_MEDIUM)

    if (end_addr[OTFBankId]) begin
      start_addr = num * 64;
      flash_op.otf_addr = start_addr;
      `uvm_info(`gfn, $sformatf("prog_flash: overflow!, roll over start address to 0x%x",
                                start_addr), UVM_MEDIUM)
    end
    is_odd = start_addr[2];

    for (int i = 0; i < num; i++) begin
      // Each flash_program_data[] entry : 4B
      // {global_cnt(16bits), lcnt(16bits)}
      for (int j = 0; j < wd; j++) begin
        if (j == 0 && is_odd == 1) flash_program_data[0] = {32{1'b1}};
        else flash_program_data[j] = {global_pat_cnt, lcnt++};
        flash_data_chunk.push_back(flash_program_data[j]);
      end
      if (wd > 1 && is_odd == 1) flash_program_data[wd] = {32{1'b1}};
      flash_data_chunk.push_back(flash_program_data[wd]);

      flash_op.addr = flash_op.otf_addr;
      // Bank : bit[19]
      flash_op.addr[TL_AW-1:OTFBankId] = bank;
      `JDBG(("full_addr:%x",flash_op.addr))
      flash_ctrl_start_op(flash_op);
      flash_ctrl_write(flash_program_data, poll_fifo_status);
      wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
      flash_op.otf_addr = flash_op.otf_addr + (4 * wd);

    end // for (int i = 0; i < num; i++)
    flash_otf_print_data64(flash_data_chunk, "wdata");
    `uvm_create_obj(flash_otf_item, exp_item)

    // Set addr to start_addr before exp_time passes
    // to scoreboard.
    flash_op.addr = start_addr;
    exp_item.cmd = flash_op;
    exp_item.dq = flash_data_chunk;
    exp_item.start_addr = start_addr;

    // scramble data
    exp_item.scramble(otp_addr_key, otp_data_key, start_addr[flash_ctrl_pkg::BusAddrByteW-2:0]);

    p_sequencer.eg_exp_ctrl_port[bank].write(exp_item);
    flash_phy_prim_agent_pkg::print_flash_data(exp_item.fq,
                                               $sformatf("fdata_%0d bank%0d", cfg.otf_ctrl_wr_sent, bank));
    global_pat_cnt++;
    cfg.otf_ctrl_wr_sent++;
  endtask // prog_flash

  // Read flash in the unit of minimum resolution (8 words).
  // 1 word : 8Byte
  // @arg: flash_op_p : command struct return updated address after write
  // @arg: bank: bank index to access flash
  // @arg: num : number of 8 words range: [1 : 32]
  // @arg: wd  : number of 4byte (TL bus unit) : default : 16

  task read_flash(ref flash_op_t flash_op, input int bank, int num, int wd = 16);
    data_q_t flash_read_data, flash_data_chunk;
    flash_otf_item exp_item;
    bit poll_fifo_status = 1;
    bit [flash_ctrl_pkg::BusAddrByteW-1:0] start_addr, end_addr;

    flash_op.op = flash_ctrl_pkg::FlashOpRead;
    flash_op.num_words = wd;
    start_addr = flash_op.otf_addr;
    end_addr = start_addr + (4 * wd) * num;
    // Check if end_addr overflows.
    // Roll over start address if this is the case.
    `uvm_info(`gfn, $sformatf("read_flash: bank:%0d  otf_addr:0x%0h, size:%0d x %0d x 4B",
                              bank, flash_op.otf_addr, num, wd), UVM_MEDIUM)

    // Ctrl read takes lower half of each bank
    // and host read takes upper half.
    if (end_addr[OTFHostId]) begin
      start_addr = num * 64;
      flash_op.otf_addr = start_addr;
      `uvm_info(`gfn, $sformatf("read_flash: overflow!, roll over start address to 0x%x",
                                start_addr), UVM_MEDIUM)
    end


    for (int i = 0; i < num; i++) begin
      flash_op.addr = flash_op.otf_addr;
      flash_op.addr[TL_AW-1:OTFBankId] = bank;
      flash_ctrl_start_op(flash_op);
      flash_ctrl_read(flash_op.num_words, flash_read_data, poll_fifo_status);
      wait_flash_op_done();

      flash_op.otf_addr = flash_op.otf_addr + (4 * wd);
      foreach(flash_read_data[i]) flash_data_chunk.push_back(flash_read_data[i]);
    end // for (int i = 0; i < num; i++)

//    flash_otf_print_data64(flash_data_chunk, "rdata");
    `uvm_create_obj(flash_otf_item, exp_item)

    flash_op.addr = start_addr;
    exp_item.cmd = flash_op;
    exp_item.start_addr = start_addr;
    exp_item.dq = flash_data_chunk;
    exp_item.fq = exp_item.dq2fq(flash_data_chunk);
    exp_item.addr_key = otp_addr_key;
    exp_item.data_key=  otp_data_key;
    p_sequencer.eg_exp_ctrl_port[bank].write(exp_item);
    cfg.otf_ctrl_rd_rcvd++;
  endtask // read_flash

  // Direct access from the host. It returns multiple of
  // 4bytes of data.
  // @arg : addr : Direct access address.
  //               At the phy interface, address_phy = addr >> 3,
  //               because phy returns data in 8byte.
  //               At the host interface, addr[2] is used for
  //               word selector s.t.
  //               addr[2]? upper 4byte : lower 4byte of phy data.
  // @arg : bank : bank index to access flash.
  // @arg : num  : number of 4byte data to read countinuously
  //               by 4 byte apart.
  task otf_direct_read(bit [OTFHostId-1:0] addr, int bank, int num);
    bit[TL_AW-1:0] tl_addr;
    bit [OTFHostId:0] end_addr;
    data_4s_t rdata;
    flash_otf_item exp_item;

    end_addr = addr + num * 4;
    if (end_addr[OTFHostId]) addr = num * 4;

    tl_addr[OTFHostId-1:2] = addr[OTFHostId-1:2];
    tl_addr[OTFBankId] = bank;
    tl_addr[OTFHostId] = 1;

    `uvm_info("direct_read", $sformatf("bank:%0d addr:0x%0h, num: %0d", bank, tl_addr, num), UVM_MEDIUM)

    for (int i = 0; i < num ; i++) begin
      do_direct_read(.addr(tl_addr), .mask('1), .blocking(1), .rdata(rdata));
      `uvm_create_obj(flash_otf_item, exp_item)
      exp_item.is_direct = 1;
      exp_item.start_addr = tl_addr;
      exp_item.addr_key = otp_addr_key;
      exp_item.data_key=  otp_data_key;
      exp_item.dq.push_back(rdata);
      p_sequencer.eg_exp_host_port[bank].write(exp_item);
      `JDBG(("SEQ: rcvd:%0d    rdata:%x",cfg.otf_host_rd_rcvd, rdata))
      cfg.otf_host_rd_rcvd++;
      tl_addr += 4;
    end
  endtask // otf_direct_read

endclass // flash_ctrl_otf_vseq
