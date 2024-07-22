// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Write and readback test. If write location is not erased, write 0's
// to mimic generic filesystem behavior.
class flash_ctrl_filesystem_support_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_filesystem_support_vseq)
  `uvm_object_new

  typedef bit [BusBankAddrW-1:0] mem_addr_q_t[$];

  // Written memory address ( flash_op.addr[19:3])
  bit            written_addr[bit[BusBankAddrW-1:0]];
  flash_op_t wr_ent_q[$];
  flash_op_t pre_wr_ent_q[$];
  flash_op_t my_op;
  data_q_t readback_data[flash_op_t];
  flash_op_t check_ent_q[$];
  mem_addr_q_t addr_q;

  constraint ctrl_num_c {ctrl_num == 1;}

  virtual task body();
    int round;

    // Don't select a partition defined as read-only
    cfg.seq_cfg.avoid_ro_partitions = 1'b1;
    cfg.seq_cfg.avoid_prog_res_fault = 1'b1;

    special_info_acc_c.constraint_mode(0);
    flash_program_data_c.constraint_mode(0);

    // Disable scramble, enable ECC
    flash_otf_region_cfg(.scr_mode(OTFCfgFalse), .ecc_mode(OTFCfgTrue));

    // Initial write to empty locations.
    repeat (100) begin
      int num;
      int bank;
      `DV_CHECK(try_create_prog_op(my_op, bank, num), "Could not create a prog flash op")
      addr_q = {addr_q, generate_all_addr(my_op)};
      wr_ent_q.push_back(my_op);
      pre_wr_ent_q.push_back(my_op);
      prog_flash(.flash_op(my_op), .bank(bank), .num(num), .wd(fractions), .store_prog_data(1));
      `uvm_info(`gfn, $sformatf("round:%0d ent:%p addr:size:%0d %p", round++, my_op,
                                addr_q.size(), addr_q), UVM_HIGH)
    end

    `uvm_info(`gfn, $sformatf("readback check stage 1"), UVM_HIGH)
    // Readback check;
    pre_wr_ent_q.shuffle();
    foreach(pre_wr_ent_q[i]) begin
      filesys_read_check(.flash_op_r(pre_wr_ent_q[i]), .use_cfg_rdata(1));
    end

    `uvm_info(`gfn, $sformatf("readback check stage 2 with 1bit error"), UVM_HIGH)
    // Readback check with 1 bit error
    pre_wr_ent_q.shuffle();
    foreach(pre_wr_ent_q[i]) begin
      filesys_read_check(.flash_op_r(pre_wr_ent_q[i]), .use_cfg_rdata(1), .serr(1));
    end

    wr_ent_q.shuffle();
    round = 0;

    // Mimicking file system behavior here.
    // If locations are from 'wr_ent_q', write all zeros.
    // Otherwise write random data.
    repeat (20) begin
      `uvm_info(`gfn, $sformatf("TEST: round:%0d", round++), UVM_MEDIUM)
      randcase
        2: begin
          my_op = wr_ent_q.pop_front();
          filesys_ctrl_prgm(.flash_op_p(my_op), .all_zero(1),
                            .wdata(readback_data[my_op]));
        end
        1: begin
          `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(rand_op,
                                                rand_op.op == FlashOpProgram;)
          // make sure all address are 8 byte aligned.
          rand_op.addr[2:0] = 'h0;
          rand_op.otf_addr[2:0] = 'h0;

          if (rand_op.num_words % 2) rand_op.num_words++;
          my_op = rand_op;
          if (is_secret_part(my_op)) continue;

          filesys_ctrl_prgm(.flash_op_p(my_op), .all_zero(0),
                            .wdata(readback_data[my_op]));
        end
      endcase
      check_ent_q.push_back(my_op);
    end

    `uvm_info(`gfn, $sformatf("readback check stage 3"), UVM_HIGH)
    // Readback check;
    foreach(check_ent_q[op]) begin
      filesys_read_check(.flash_op_r(check_ent_q[op]));
    end

    `uvm_info(`gfn, $sformatf("readback check stage 4 with 1 bit error"), UVM_HIGH)
    // Readback check with 1 bit error
    foreach(check_ent_q[op]) begin
      filesys_read_check(.flash_op_r(check_ent_q[op]), .serr(1));
    end

  endtask

  // Helper task to issue a flash program op.
  local task issue_flash_prog(flash_op_t op, data_q_t data);
    bit poll_fifo_status = 1;
    `uvm_info(`gfn, "Issuing flash write op:", UVM_MEDIUM)
    flash_ctrl_start_op(op);
    flash_ctrl_write(data, poll_fifo_status);
    wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
  endtask

  // Program flash.
  // Program all 0 or random data depends on 'all_zero' value.
  // If program address is in global 'addr_q', program all zero
  // to the address.
  // After program, store write data for readback check.
  task filesys_ctrl_prgm(flash_op_t flash_op_p, bit all_zero, output data_q_t wdata);
    bit [BusBankAddrW-1:0] mem_addr = (flash_op_p.addr >> 3);
    bit                    ovwr_zero = 0;

    flash_op_p.op = FlashOpProgram;
    `uvm_info(`gfn, $sformatf("PROGRAM ADDRESS: 0x%0h flash_op:%p is_secret:%b",
              flash_op_p.addr, flash_op_p, is_secret_part(flash_op_p)), UVM_MEDIUM)
    // Randomize Write Data
    for (int j = 0; j < flash_op_p.num_words; j++) begin
      if (j % 2 == 0) begin
        foreach (addr_q[i]) begin
          if (mem_addr == addr_q[i]) begin
            ovwr_zero = 1;
            break;
          end
        end
      end

      flash_program_data[j] = (all_zero | ovwr_zero)? 'h0 : $urandom();
      wdata.push_back(flash_program_data[j]);
      if (j % 2 == 1) begin
        ovwr_zero = 0;
        mem_addr++;
      end
    end
    // If the op spills over a program window, break it into two.
    if (in_different_prog_win(flash_op_p.addr,
                              flash_op_p.addr + 4 * flash_op_p.num_words - 1)) begin
      flash_op_t first_op, second_op;
      addr_t split_addr = round_to_prog_resolution(flash_op_p.addr + 4 * flash_op_p.num_words - 1);
      `DV_CHECK_LE(flash_op_p.num_words, 16)
      first_op = flash_op_p;
      first_op.num_words = (split_addr - flash_op_p.addr) / 4;
      print_flash_op(flash_op_p, UVM_MEDIUM);
      `uvm_info(`gfn, $sformatf(
                "splitting at addr:%x, first wd:%x", split_addr, first_op.num_words), UVM_MEDIUM)
      issue_flash_prog(first_op, flash_program_data[0:first_op.num_words-1]);
      second_op = flash_op_p;
      second_op.addr = split_addr;
      second_op.otf_addr = split_addr;
      second_op.num_words = flash_op_p.num_words - first_op.num_words;
      issue_flash_prog(second_op, flash_program_data[first_op.num_words:flash_op_p.num_words - 1]);
    end else begin
      issue_flash_prog(flash_op_p, flash_program_data);
    end
  endtask : filesys_ctrl_prgm

  // Read data either from host or controller, and compare with
  // readback_data[flash_op_t].
  task filesys_read_check(flash_op_t flash_op_r, bit use_cfg_rdata = 0, bit serr = 0);
    data_q_t read_data, ref_data;
    flash_op_r.op = FlashOpRead;
    `uvm_info("read_check", $sformatf("%p", flash_op_r), UVM_MEDIUM)
    if (flash_op_r.partition == FlashPartData) begin
      randcase
        1: begin
          `uvm_info(`gfn, "send ctrl_read", UVM_MEDIUM)
          filesys_ctrl_read(flash_op_r, read_data, serr);
        end
        1: begin
          `uvm_info(`gfn, "send host_read", UVM_MEDIUM)
          filesys_host_read(flash_op_r, read_data, serr);
        end
      endcase // randcase
    end else begin // if (flash_op_r.partition == FlashPartData)
      `uvm_info(`gfn, "send ctrl_read", UVM_MEDIUM)
      filesys_ctrl_read(flash_op_r, read_data, serr);
    end

    ref_data = (use_cfg_rdata)? cfg.prog_data[flash_op_r] : readback_data[flash_op_r];
    for (int i = 0; i < ref_data.size(); i++) begin
      `DV_CHECK_EQ(read_data[i], ref_data[i],
                   $sformatf("read_check:%0d ", i))
    end
  endtask : filesys_read_check

  // All addresses are 8byte aligned.
  task filesys_ctrl_read(flash_op_t flash_op_r, output data_q_t rdata, input bit serr);
    bit poll_fifo_status = 1;
    int size;
    flash_op_r.op = FlashOpRead;
    `uvm_info(`gfn, $sformatf("filesys_ctrl_read: flash_op:%p is_secret:%b",
               flash_op_r, is_secret_part(flash_op_r)), UVM_MEDIUM)

    rdata = '{};
    size = flash_op_r.num_words / 2;
    if (serr) begin
      filesystem_add_bit_err(flash_op_r.partition, flash_op_r.addr, ReadTaskCtrl, size);
    end
    flash_ctrl_start_op(flash_op_r);
    flash_ctrl_read(flash_op_r.num_words, rdata, poll_fifo_status);
    wait_flash_op_done();
  endtask : filesys_ctrl_read

  task filesys_host_read(flash_op_t flash_op_r, output data_q_t rdata, input bit serr);
    bit [TL_AW-1:0] tl_addr;
    bit             completed;
    data_4s_t unit_rdata;
    tl_addr = flash_op_r.addr;
    rdata = '{};

    for (int i = 0; i < flash_op_r.num_words; i++) begin
      if (serr & (i % 2 == 0)) begin
        filesystem_add_bit_err(flash_op_r.partition, tl_addr, ReadTaskHost, 1);
      end
      do_direct_read(.addr(tl_addr), .mask('1), .blocking(1), .rdata(unit_rdata),
                     .completed(completed));
      rdata.push_back(unit_rdata);
      tl_addr += 4;
    end
  endtask : filesys_host_read

  // Create all addresses for the flash_op from the start address
  // in the resolution of 8 bytes
  function mem_addr_q_t generate_all_addr(flash_op_t flash_op);
    // For odd numbers, add one more address.
    int addr_end = (flash_op.num_words + 1) / 2;
    for (int i = 0; i < addr_end; i++) begin
      generate_all_addr.push_back((flash_op.addr >> 3));
      flash_op.addr += 8;
    end
  endfunction : generate_all_addr

  function void filesystem_add_bit_err(flash_dv_part_e partition, addr_t addr, read_task_e caller,
                                       int size);
    int err_idx, bank;
    addr_t per_bank_addr;
    bit [flash_phy_pkg::FullDataWidth-1:0] mem_data;

    bank = addr[OTFBankId];
    for (int i = 0; i < size; i++) begin
      per_bank_addr = addr;
      per_bank_addr[31:OTFBankId] = 'h0;

      if (!cfg.address_has_serr(addr, partition)) begin
        err_idx = $urandom_range(0, 75);
        cfg.add_serr(addr, partition, caller, err_idx);
        cfg.flash_bit_flip(cfg.mem_bkdr_util_h[partition][bank], per_bank_addr, err_idx);
        // Flip the same bit in the reference mem model.
        if (partition == FlashPartData) begin
          mem_data = cfg.otf_scb_h.data_mem[bank][per_bank_addr>>3];
          mem_data[err_idx] = ~mem_data[err_idx];
          cfg.otf_scb_h.data_mem[bank][per_bank_addr>>3] = mem_data;
        end else begin
          mem_data = cfg.otf_scb_h.info_mem[bank][partition>>1][per_bank_addr>>3];
          mem_data[err_idx] = ~mem_data[err_idx];
          cfg.otf_scb_h.info_mem[bank][partition>>1][per_bank_addr>>3] = mem_data;
        end
      end
      addr += 8;
    end
  endfunction : filesystem_add_bit_err

endclass : flash_ctrl_filesystem_support_vseq
