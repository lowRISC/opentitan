// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will write a random values to combo detect registers
// and check for the combo detect interrupt
class sysrst_ctrl_combo_detect_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_combo_detect_vseq)

  `uvm_object_new
   rand uvm_reg_data_t trigger_combo, set_action;
   rand uint16_t set_duration, set_pulse_width, set_key_timer;

   constraint trigger_combo_c {trigger_combo != 0;}

  task body();
    uvm_reg_data_t rdata_com_sel_ctl, rdata;
    bit int_act_set, bat_act_set, ec_act_set, rst_act_set;

    // Enable interrupt
    ral.intr_enable.set(1);
    csr_update(ral.intr_enable);

    `uvm_info(`gfn, "Starting the body from combo detect", UVM_LOW)

    // Disable the override function
    ral.pin_out_ctl.ec_rst_l.set(0);
    csr_update(ral.pin_out_ctl);

    // Enable input keys to trigger the combo
    csr_wr(ral.com_sel_ctl[0], trigger_combo);
    `uvm_info(`gfn, $sformatf("Write data of com_sel_ctl_0 register:%0h",
                               trigger_combo), UVM_LOW)

    // Set the duration for combo to pressed
    csr_wr(ral.com_det_ctl[0], set_duration);
    `uvm_info(`gfn, $sformatf("Write data of com_det_ctl_0 register:%0h",
                               set_duration), UVM_LOW);

    // Set the trigger action
    csr_wr(ral.com_out_ctl[0], 'hf);
    `uvm_info(`gfn, $sformatf("Write data of com_out_ctl_0 register:%0h",
                               set_action), UVM_LOW);

    // Set the ec_rst_0 pulse width
    csr_wr(ral.ec_rst_ctl, set_pulse_width);
    `uvm_info(`gfn, $sformatf("Write data of ec_rst_ctl register:%0h",
                               set_pulse_width), UVM_LOW);

    // Set the key triggered debounce timer
    csr_wr(ral.key_intr_debounce_ctl, set_key_timer);
    `uvm_info(`gfn, $sformatf("Write data of key_intr_debounce_ctl register:%0h",
                               set_key_timer), UVM_LOW);

    repeat ($urandom_range(2,10)) begin
     // Trigger the input pins
     cfg.clk_aon_rst_vif.wait_clks(1);
     cfg.vif.randomize_input();
    end

    fork
    begin
      // Wait for debounce + detect timer
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer + set_duration);
    end
    begin
      // Wait for the ec_rst_timer
      cfg.clk_aon_rst_vif.wait_clks(set_pulse_width);
      `DV_CHECK_EQ(cfg.vif.ec_rst_l_out, 1);
    end
    join

    // Check if the interrupt has raised
    // NOTE: The interrupt will only raise if the interrupt
    // combo action is set
    int_act_set = get_field_val(ral.com_out_ctl[0].interrupt, set_action);
    bat_act_set = get_field_val(ral.com_out_ctl[0].bat_disable, set_action);
    ec_act_set = get_field_val(ral.com_out_ctl[0].ec_rst, set_action);
    rst_act_set = get_field_val(ral.com_out_ctl[0].rst_req, set_action);

    if (int_act_set == 1) begin
     while (rdata != 1) begin
      csr_rd(.ptr(ral.combo_intr_status), .value(rdata));
     end

     // Write to clear the interrupt
     csr_wr(ral.combo_intr_status, 'h1);

     cfg.clk_aon_rst_vif.wait_clks(20);
     // check if the interrupt is cleared
     csr_rd_check(ral.combo_intr_status, .compare_value(0));
    end

    // If bat_disable trigger action is set then check if there is a transition
    // on cio_bat_disable_o signal
    if (bat_act_set == 1) begin
     `DV_CHECK_EQ(cfg.vif.bat_disable, 1);
    end

    // If reset req trigger action is set then check if there is a event
    // on aon_sysrst_ctrl_rst_req_o pin
    if (rst_act_set == 1) begin
     `DV_CHECK_EQ(cfg.vif.sysrst_ctrl_rst_req, 1);
    end

    cfg.clk_aon_rst_vif.wait_clks(20);
  endtask : body

endclass : sysrst_ctrl_combo_detect_vseq

