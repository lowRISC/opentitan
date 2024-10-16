// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Directed test to check flash_ctrl.single_err_cnt
// Use low error injection pct to avoid counter saturation.
// Counter can be saturated but not all the time.
class flash_ctrl_serr_counter_vseq extends flash_ctrl_rw_vseq;
  `uvm_object_utils(flash_ctrl_serr_counter_vseq)
  `uvm_object_new

  task post_body();
    uvm_reg_data_t data;
    csr_rd(.ptr(ral.ecc_single_err_cnt[0]), .value(data));
    `DV_CHECK_EQ(data[7:0], cfg.serr_cnt[0])
    `DV_CHECK_EQ(data[15:8], cfg.serr_cnt[1])
  endtask
endclass // flash_ctrl_serr_counter_vseq
