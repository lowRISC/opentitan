// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class sysrst_ctrl_smoke_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_smoke_vseq)

  `uvm_object_new

  constraint num_trans_c {num_trans == 20;}

  task body();
   `uvm_info(`gfn, "Starting the body from smoke_seq", UVM_LOW)

    repeat (num_trans) begin

      // Randomize the input pins
      cfg.vif.randomize_input();

      // In normal mode sysrst_ctrl should pass the input pins data to output pins as it is
      cfg.clk_aon_rst_vif.wait_clks(1);
      `DV_CHECK_EQ(cfg.vif.key0_in, cfg.vif.key0_out)
      `DV_CHECK_EQ(cfg.vif.key1_in, cfg.vif.key1_out)
      `DV_CHECK_EQ(cfg.vif.key2_in, cfg.vif.key2_out)
      `DV_CHECK_EQ(cfg.vif.pwrb_in, cfg.vif.pwrb_out)
      // Input pin flash_wp_l_in should not affect flash_wp_l_o output pin
      `DV_CHECK_EQ(cfg.vif.flash_wp_l, 0)
    end
  endtask : body

endclass : sysrst_ctrl_smoke_vseq
