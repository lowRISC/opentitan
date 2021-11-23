// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will assert the ec_rst_out_l and raise an interrupt when certain combos are detected.
class sysrst_ctrl_combo_detect_ec_rst_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_combo_detect_ec_rst_vseq)

  `uvm_object_new

   task body();
    uvm_reg_data_t rdata, rdata1;

    `uvm_info(`gfn, "Starting the body from combo detect ec_rst", UVM_LOW)

    // Enable the override function and set the override value for ec_rst_l pin
    ral.pin_out_ctl.ec_rst_l.set(1);
    csr_update(ral.pin_out_ctl);

    ral.pin_out_value.ec_rst_l.set(1);
    csr_update(ral.pin_out_value);

    ral.pin_allowed_ctl.ec_rst_l_0.set(1);
    ral.pin_allowed_ctl.ec_rst_l_1.set(1);
    csr_update(ral.pin_allowed_ctl);

    // Enabled key0_in, key1_in, key2_in to trigger the combo
    csr_wr(ral.com_sel_ctl[0], 'h7);

    // Set the duration for combo to pressed
    csr_wr(ral.com_det_ctl[0],'h5) ;

    // Enabled ec_rst_0 action
    csr_wr(ral.com_out_ctl[0], 'h6);

    // Set the ec_rst_0 pulse width
    csr_wr(ral.ec_rst_ctl, 'h5);

    repeat ($urandom_range(1,3)) begin
      // Trigger the input pins
      cfg.vif.key0_in = 1;
      cfg.vif.key1_in = 1;
      cfg.vif.key2_in = 1;
      #50us;
      cfg.vif.key0_in = 0;
      cfg.vif.key1_in = 0;
      cfg.vif.key2_in = 0;
      #50us;
    end

    // Wait for interrupt to raise
    #100us;

    csr_rd_check(.ptr(ral.combo_intr_status), .compare_value(1));
    `uvm_info(`gfn, ral.combo_intr_status.sprint(), UVM_MEDIUM)

    // Write to clear the interrupt
    csr_wr(ral.combo_intr_status, 'h1);

    #100us;
    // check if the interrupt is cleared
    csr_rd_check(.ptr(ral.combo_intr_status), .compare_value(0));

    #100us;
  endtask : body

endclass : sysrst_ctrl_combo_detect_ec_rst_vseq
