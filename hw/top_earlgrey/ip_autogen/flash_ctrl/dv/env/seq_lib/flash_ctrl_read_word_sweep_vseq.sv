// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Read fraction of the page.
// fraction size starts from 1 word (4byte) and increased by 1 word in each round.
// For error injection to work the data must be initialized, done via mem_bkdr.
//
// There are two enhancements needed here:
// - Initialize the data right before each read
// - Detect addresses out of partition bounds and terminate within the loop.
class flash_ctrl_read_word_sweep_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_read_word_sweep_vseq)
  `uvm_object_new

  // This is to avoid errors due to the address ending up out-of-bounds as they are incremented.
  // It begs a better way to handle this, like just stopping the loop below.
  constraint partition_c {rand_op.partition == FlashPartData;}

  localparam int InitializedMemBytes = 1024;

  virtual task body();
    flash_op_t ctrl;
    addr_t start_addr, max_addr;
    addr_t addr;

    int num, bank;
    int mywd;

    `DV_CHECK_RANDOMIZE_FATAL(this)

    bank = rand_op.addr[OTFBankId];
    start_addr = rand_op.addr;
    max_addr = start_addr + InitializedMemBytes - 1;

    // It may be better to initialize the data right before each individual read.
    `uvm_info("read_word_sweep", $sformatf(
              "Initializing data from addr:0x%x to:0x%x", start_addr, max_addr),
              UVM_MEDIUM)
    cfg.update_otf_mem_read_zone(rand_op.partition, bank, start_addr, max_addr);

    ctrl = rand_op;
    num = 1;
    mywd = 1;
    addr = start_addr;
    repeat(20) begin
      addr_t end_addr = addr + num * mywd * 4 - 1;
      // Don't read uninitialized memory to avoid trouble.
      if (end_addr > max_addr) break;
      ctrl.addr = addr;
      ctrl.otf_addr = addr;
      print_flash_op(ctrl, UVM_MEDIUM);
      `uvm_info("read_word_sweep", $sformatf(
                "Reading from addr:0x%x, otf_addr:0x%x, num:%0d, wd:%0d",
                ctrl.addr, ctrl.otf_addr, num, mywd),
                UVM_MEDIUM)
      read_flash(ctrl, bank, num, mywd);
      addr += num * mywd * 4;
      mywd = (mywd % 16) + 1;
    end
  endtask

endclass : flash_ctrl_read_word_sweep_vseq
