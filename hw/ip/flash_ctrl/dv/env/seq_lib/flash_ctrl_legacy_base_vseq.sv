// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_legacy_base_vseq extends flash_ctrl_otf_base_vseq;

  `uvm_object_utils(flash_ctrl_legacy_base_vseq)
  `uvm_object_new
  flash_op_t ctrl;
  int num, bank;

  virtual task pre_start();
    super.pre_start();

    for (int j = 0; j < NumBanks; j++) begin
      for (int i = 0; i < PagesPerBank; i++) load_otf_mem_page(FlashPartData, j, i);
      for (int i = 0; i < InfoTypeSize[0]; i++) load_otf_mem_page(FlashPartInfo, j, i);
      for (int i = 0; i < InfoTypeSize[1]; i++) load_otf_mem_page(FlashPartInfo1, j, i);
      for (int i = 0; i < InfoTypeSize[2]; i++) load_otf_mem_page(FlashPartInfo2, j, i);
    end

    cfg.scb_h.do_alert_check = 0;
    expect_fatal_alerts = 1;
  endtask
endclass
