// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_legacy_base_vseq extends flash_ctrl_otf_base_vseq;

  `uvm_object_utils(flash_ctrl_legacy_base_vseq)
  `uvm_object_new
  flash_op_t ctrl;
  int num, bank;

  constraint rand_op_c {
    solve fractions before rand_op.addr;
    solve flash_program_data before rand_op;
    solve rand_op.partition before rand_op.prog_sel, rand_op.addr;
    solve rand_op.addr before rand_op.otf_addr;
    solve rand_op.addr before rand_op.num_words;
    if (cfg.seq_cfg.op_readonly_on_info_partition) {
      if (cfg.seq_cfg.avoid_ro_partitions) {
        rand_op.partition != FlashPartInfo;
      } else {
        rand_op.partition == FlashPartInfo -> rand_op.op == flash_ctrl_pkg::FlashOpRead;
      }
    }
    if (cfg.seq_cfg.op_readonly_on_info1_partition) {
      if (cfg.seq_cfg.avoid_ro_partitions) {
        rand_op.partition != FlashPartInfo1;
      } else {
        rand_op.partition == FlashPartInfo1 -> rand_op.op == flash_ctrl_pkg::FlashOpRead;
      }
    }
    rand_op.partition dist { FlashPartData := 1, [FlashPartInfo:FlashPartInfo2] :/ 1};
    rand_op.addr[TL_AW-1:BusAddrByteW] == 'h0;
    rand_op.addr[1:0] == 'h0;
    cfg.seq_cfg.addr_flash_word_aligned -> rand_op.addr[2] == 1'b0;
    // If address starts from 0x4 and full prog_win size access(16),
    // transaction creates prog_win error.
    // To prevent that, make full size access always start from address[2:0] == 0.
    if (fractions == 16) rand_op.addr[2] == 0;
    if (rand_op.partition != FlashPartData) {
      rand_op.addr inside
          {[0:InfoTypeBytes[rand_op.partition>>1]-(FlashBankBytesPerWord*fractions)]};
      rand_op.prog_sel == 1;
    } else {
      rand_op.prog_sel == 0;
    }
    if (cfg.ecc_mode > FlashEccEnabled) {
      if (rand_op.partition == FlashPartData) {
        rand_op.addr[18:17] == cfg.tgt_pre[rand_op.partition][cfg.seq_cfg.ecc_err_target];
      } else {
        rand_op.addr[10:9] == cfg.tgt_pre[rand_op.partition][cfg.seq_cfg.ecc_err_target];
      }
    }
    rand_op.otf_addr == rand_op.addr[BusAddrByteW-2:0];
    rand_op.num_words == fractions;
    rand_op.addr[5:0] + ((rand_op.num_words - 1) * 4) < 64;
  }

  virtual task pre_start();
    super.pre_start();
    cfg.preload_mem();
    cfg.scb_h.do_alert_check = 0;
    expect_fatal_alerts = 1;
  endtask
endclass
