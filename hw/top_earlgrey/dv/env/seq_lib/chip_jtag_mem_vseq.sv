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
      test_mem_rw(.mem(test_mems[i]), .max_access(128));
    end
  endtask : body

endclass
