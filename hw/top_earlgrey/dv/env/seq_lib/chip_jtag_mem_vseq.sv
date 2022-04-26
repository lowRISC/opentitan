// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test write and read back test through jtag interface for
// following memories : otbn.imem, otbn.dmem, sram_ctrl_main_ram.ram, sram_ctrl_ret_aon_ram.ram
// Also preload random data to rom_ctrl_rom.rom and check read data integrity
// through jtag interface
class chip_jtag_mem_vseq extends chip_common_vseq;
  uvm_mem test_mems[$];
  `uvm_object_utils(chip_jtag_mem_vseq)

  `uvm_object_new

  virtual task pre_start();
    select_jtag = SelectRVJtagTap;
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
    super.pre_start();
  endtask

  virtual task body();
    uvm_mem mems[$];
    jtag_riscv_dm_activation_seq jtag_dm_activation_seq =
        jtag_riscv_dm_activation_seq::type_id::create("jtag_dm_activation_seq");

    cfg.m_jtag_riscv_agent_cfg.allow_errors = 1;
    jtag_dm_activation_seq.start(p_sequencer.jtag_sequencer_h);
    cfg.m_jtag_riscv_agent_cfg.allow_errors = 0;

    foreach (cfg.ral_models[i]) begin
      cfg.ral_models[i].get_memories(mems);
    end

    foreach (mems[i]) begin
      if (mems[i].get_name() inside {"ram", "imem", "dmem"} ||
          mems[i].get_block().get_name() == "rom_ctrl_rom") begin
        test_mems.push_back(mems[i]);
      end
    end

    `uvm_info(`gfn, $sformatf("Number of Test Mems : %0d",test_mems.size()), UVM_MEDIUM)
    test_mems.shuffle();

    for (int i = 0;i < test_mems.size(); ++i) begin
        access_mem(test_mems[i]);
    end
  endtask : body

  task access_mem(uvm_mem mem);
    uvm_reg_data_t rdata;
    int wdata, exp_data[$]; // cause all data is 32bit wide in this test
    int offmax = mem.get_size() - 1;
    int sizemax = offmax / 4;
    int st, sz;
    int byte_addr;
    st = $urandom_range(0, offmax);
    // set the maximum transaction per memory to 2K * 4Byte
    if (sizemax > 2048) sizemax = 2048;

    sz = $urandom_range(1, sizemax);
    `uvm_info(`gfn, $sformatf("Mem write to %s  offset:%0d size: %0d",
                              mem.get_full_name(), st, sz), UVM_MEDIUM)

    for (int i = 0; i < sz; ++i) begin
      wdata = $urandom();
      exp_data.push_back(wdata);

      if (mem.get_access() == "RW") begin
        mem_wr(.ptr(mem), .offset((st + i) % (offmax + 1)), .data(wdata));
      end else begin // if (mem.get_access() == "RW")
        // deposit random data to rom
        byte_addr = ((st + i) % (offmax + 1)) * 4;
        cfg.mem_bkdr_util_h[Rom].rom_encrypt_write32_integ(.addr(byte_addr), .data(wdata),
                                                           .key(RndCnstRomCtrlScrKey),
                                                           .nonce(RndCnstRomCtrlScrNonce),
                                                           .scramble_data(1));
      end
    end

    `uvm_info(`gfn, $sformatf("write to %s is complete, read back start...",
                                mem.get_full_name()), UVM_MEDIUM)
    for (int i = 0; i < sz; ++i) begin
      mem_rd(.ptr(mem), .offset((st + i) % (offmax + 1)), .data(rdata));
      `DV_CHECK_EQ((int'(rdata)), exp_data[i],
                   $sformatf("read back check for offset:%0d failed",
                             ((st + i) % (offmax + 1))))
    end
    `uvm_info(`gfn, $sformatf("read check from %s is complete",
                              mem.get_full_name()), UVM_MEDIUM)

  endtask // run_mem_rw

endclass
