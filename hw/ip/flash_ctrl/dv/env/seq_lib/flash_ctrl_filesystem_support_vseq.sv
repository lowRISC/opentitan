// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Write and readback test over randomly erased pages.
class flash_ctrl_filesystem_support_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_filesystem_support_vseq)
  `uvm_object_new

  typedef struct packed {
    bit          bank;
    int          page;
    flash_dv_part_e part;
  } pages_t;

  data_q_t readback_data[pages_t];
  virtual task body();
    bit erased_page[pages_t];
    pages_t fs_wr_page[$];
    pages_t mypage;
    bit all_zero;
    special_info_acc_c.constraint_mode(0);
    allow_spec_info_acc = 3'h7;
    // Disable scramble, enable ECC
    flash_otf_region_cfg(.scr_mode(OTFCfgFalse), .ecc_mode(OTFCfgTrue));

    // Randomize flash with policy
    for (int j = 0; j < NumBanks; j++) begin
      for (int i = 0; i < PagesPerBank; i++) load_otf_mem_page(FlashPartData, j, i);
      for (int i = 0; i < InfoTypeSize[0]; i++) load_otf_mem_page(FlashPartInfo, j, i);
      for (int i = 0; i < InfoTypeSize[1]; i++) load_otf_mem_page(FlashPartInfo1, j, i);
      for (int i = 0; i < InfoTypeSize[2]; i++) load_otf_mem_page(FlashPartInfo2, j, i);
    end

    // Erase random pages. Add bank erase later
    repeat (50) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rand_op)

      mypage.bank = rand_op.addr[OTFBankId];
      // use 9bit pages (0~511)
      mypage.page = cfg.addr2page(rand_op.addr);
      mypage.part = rand_op.partition;

      erase_flash(rand_op, mypage.bank);
      `uvm_info("erased_page", $sformatf("%p", mypage), UVM_MEDIUM)
      erased_page[mypage] = 1;
    end

    repeat (10) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rand_op)
      mypage.bank = rand_op.addr[OTFBankId];
      // use 9bit pages (0~511)
      mypage.page = cfg.addr2page(rand_op.addr);
      mypage.part = rand_op.partition;
      // Prevent write to the same address
      if (readback_data.exists(mypage)) continue;

      all_zero = (erased_page.exists(mypage))? 0 : 1;
      filesys_ctrl_prgm_page(.flash_op_p(rand_op), .all_zero(all_zero),
                             .wdata(readback_data[mypage]));
      `uvm_info("program_page", $sformatf("%p all_zero:%0b", mypage, all_zero), UVM_MEDIUM)
      `uvm_info("program_page", $sformatf("size:%0d data: %p",
                            readback_data[mypage].size(), readback_data[mypage]), UVM_HIGH)
      fs_wr_page.push_back(mypage);
    end // repeat (10)

    fs_wr_page.shuffle();

    foreach(fs_wr_page[page]) begin
      `uvm_info("read_check", $sformatf("%p", fs_wr_page[page]), UVM_MEDIUM)
      filesys_read_check(fs_wr_page[page]);
    end

  endtask

  // Program page.
  // If the page is in the erased page list, write random data
  // else write all 0's.
  // Afte program, store write data for readback check.
  task filesys_ctrl_prgm_page(flash_op_t flash_op_p, bit all_zero, output data_q_t wdata);
    bit poll_fifo_status = 1;
    flash_op_p.op = flash_ctrl_pkg::FlashOpProgram;
    flash_op_p.num_words = 16;
    flash_op_p.addr = {flash_op_p.addr[19:11], {11{1'b0}}};
    for (int i = 0; i < 32; i++) begin
      `uvm_info(`gfn, $sformatf("PROGRAM ADDRESS: 0x%0h", flash_op_p.addr), UVM_HIGH)
      // Randomize Write Data
      for (int j = 0; j < 16; j++) begin
        flash_program_data[j] = (all_zero)? 'h0 : $urandom();
        wdata.push_back(flash_program_data[j]);
      end

      flash_ctrl_start_op(flash_op_p);
      flash_ctrl_write(flash_program_data, poll_fifo_status);
      wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
      flash_op_p.addr = flash_op_p.addr + 64;  //64B was written, 16 words
    end
  endtask // filesys_ctrl_prgm_page

  // Read page either from host or controller, and compare with
  // readback_data[pages_t].
  task filesys_read_check(pages_t page);
    data_q_t read_data, ref_data;
    if (page.part == FlashPartData) begin
      randcase
        1: begin
          `uvm_info(`gfn, "send ctrl_read", UVM_MEDIUM)
          filesys_ctrl_read(page, read_data);
        end
        1: begin
          `uvm_info(`gfn, "send host_read", UVM_MEDIUM)
          filesys_host_read(page, read_data);
        end
      endcase // randcase
    end else begin // if (page.part == FlashPartData)
      `uvm_info(`gfn, "send ctrl_read", UVM_MEDIUM)
      filesys_ctrl_read(page, read_data);
    end

    ref_data = readback_data[page];
    for (int i = 0; i < ref_data.size(); i++) begin
      `DV_CHECK_EQ(read_data[i], ref_data[i],
                   $sformatf("read_check:%0d ", i))
    end
  endtask // filesys_read_check

  task filesys_ctrl_read(pages_t page_entry, output data_q_t rdata);
    flash_op_t flash_op_r;
    data_q_t flash_read_data;
    bit poll_fifo_status = 1;
    flash_op_r.op = flash_ctrl_pkg::FlashOpRead;
    flash_op_r.num_words = 16;
    flash_op_r.addr[OTFBankId] = page_entry.bank;
    flash_op_r.addr[OTFBankId-1:11] = page_entry.page;
    flash_op_r.partition = page_entry.part;
    rdata = '{};
    for (int i = 0; i < 32; i++) begin
      flash_ctrl_start_op(flash_op_r);
      flash_ctrl_read(flash_op_r.num_words, flash_read_data, poll_fifo_status);
      wait_flash_op_done();
      flash_op_r.addr = flash_op_r.addr + 64;  //64B was read, 16 words
      rdata = {rdata, flash_read_data};
    end
  endtask // filesys_ctrl_read

  task filesys_host_read(pages_t page_entry, output data_q_t rdata);
    bit [TL_AW-1:0] tl_addr;
    bit             completed;
    data_4s_t unit_rdata;

    tl_addr[OTFBankId] = page_entry.bank;
    tl_addr[OTFBankId-1:11] = page_entry.page;
    rdata = '{};
    // 2048 byte read
    for (int i = 0; i < 512; i++) begin
      do_direct_read(.addr(tl_addr), .mask('1), .blocking(1), .rdata(unit_rdata),
                     .completed(completed));
      rdata.push_back(unit_rdata);
    end
  endtask // filesys_host_read

endclass // flash_ctrl_filesystem_support_vseq
