// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence set dmactive, then toggle ndm reset
class chip_rv_dm_ndm_reset_vseq extends chip_jtag_base_vseq;
  `uvm_object_utils(chip_rv_dm_ndm_reset_vseq)
  `uvm_object_new

  virtual task body();
    super.body();
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "wait for ndm reset",
             "Timedout waiting for ndm reset.")
    cfg.clk_rst_vif.wait_clks(10);
    debug_mode_en();
    cfg.clk_rst_vif.wait_clks(10);
    ndm_reset_off();
    cfg.clk_rst_vif.wait_clks(10);
  endtask // body

endclass // chip_rv_dm_ndm_reset_vseq
