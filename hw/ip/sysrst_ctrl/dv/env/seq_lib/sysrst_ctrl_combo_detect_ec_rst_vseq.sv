// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will assert the ec_rst_out_l and raise an interrupt
// when certain combos are detected.
class sysrst_ctrl_combo_detect_ec_rst_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_combo_detect_ec_rst_vseq)

  `uvm_object_new

  rand int wait_cycles;
  rand uvm_reg_data_t detect_timer, debounce_timer;

  constraint wait_cycles_c {wait_cycles dist {
    [15 : 25] :/5,
    25 :/95
    };
  }

  constraint detect_timer_c {detect_timer == 'h5;}
  constraint debounce_timer_c {debounce_timer == 'h20;}

  task drive_input();
    // Trigger the input pins
    cfg.vif.key0_in = 1;
    cfg.vif.key1_in = 1;
    cfg.vif.key2_in = 1;
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(1,10));
    cfg.vif.key0_in = 0;
    cfg.vif.key1_in = 0;
    cfg.vif.key2_in = 0;
    cfg.clk_aon_rst_vif.wait_clks(wait_cycles);
    cfg.vif.key0_in = 1;
    cfg.vif.key1_in = 1;
    cfg.vif.key2_in = 1;
  endtask

  task body();
    uvm_reg_data_t rdata = 0;

    `uvm_info(`gfn, "Starting the body from combo detect ec_rst", UVM_LOW)

    // Enable the override function and set the override value for ec_rst_l pin
    ral.pin_out_ctl.ec_rst_l.set(0);
    csr_update(ral.pin_out_ctl);

    // Enabled key0_in, key1_in, key2_in to trigger the combo
    csr_wr(ral.com_sel_ctl[0], 'h7);

    // Set the duration for combo to pressed
    csr_wr(ral.com_det_ctl[0], detect_timer);

    // Enabled ec_rst_0 action
    csr_wr(ral.com_out_ctl[0], 'h6);

    // Set the ec_rst_0 pulse width
    csr_wr(ral.ec_rst_ctl, 'h10);

    // Set the key triggered debounce timer
    csr_wr(ral.key_intr_debounce_ctl, debounce_timer);

    // It takes 2-3 clock cycles to sync the register values
    cfg.clk_aon_rst_vif.wait_clks(2);

    drive_input();

    `uvm_info(`gfn, $sformatf("Value of wait_cycles:%0d", wait_cycles), UVM_LOW)
    if (wait_cycles >= (debounce_timer + detect_timer)) begin
      // It takes 2-3 clock cycles to sync the interrupt value
      // Read the combo status register
      cfg.clk_aon_rst_vif.wait_clks(2);
      csr_rd_check(.ptr(ral.combo_intr_status), .compare_value(1));

      // Write to clear the interrupt
      csr_wr(ral.combo_intr_status, 'h1);

      cfg.clk_aon_rst_vif.wait_clks(20);
      // check if the interrupt is cleared
      csr_rd_check(.ptr(ral.combo_intr_status), .compare_value(0));
    end else begin
      // check there is no interrupt
      csr_rd_check(.ptr(ral.combo_intr_status), .compare_value(0));
    end
    cfg.clk_aon_rst_vif.wait_clks(20);
  endtask : body

endclass : sysrst_ctrl_combo_detect_ec_rst_vseq
