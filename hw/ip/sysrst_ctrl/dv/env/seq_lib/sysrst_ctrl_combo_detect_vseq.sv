// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will write a random values to combo detect registers
// and check for the combo detect interrupt
class sysrst_ctrl_combo_detect_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_combo_detect_vseq)

  `uvm_object_new
  rand uvm_reg_data_t set_action;
  rand bit[4:0] trigger_combo;
  rand uint16_t set_duration, set_pulse_width, set_key_timer;
  rand uint16_t cycles;

  constraint num_trans_c {num_trans == 3;}

  constraint set_duration_c {
    set_duration dist {
      [10:100] :/ 95,
      [101:$]   :/ 5
    };
  }

  constraint set_pulse_width_c {
    set_pulse_width dist {
      [10:100] :/ 95,
      [101:$]   :/ 5
    };
  }

  constraint set_key_timer_c {
    set_key_timer dist {
      [10:100] :/ 95,
      [101:$]   :/ 5
    };
  }

  constraint cycles_c {
    cycles dist {
      [(set_duration + set_key_timer) - 10 : (set_duration + set_key_timer)] :/ 5,
      [(set_duration + set_key_timer) : (set_duration + set_key_timer) + 3]   :/ 95
    };
  }

  function bit get_combo_trigger();
    logic [4:0] in;
    in[0] = cfg.vif.key0_in;
    in[1] = cfg.vif.key1_in;
    in[2] = cfg.vif.key2_in;
    in[3] = cfg.vif.pwrb_in;
    in[4] = cfg.vif.ac_present;
    return  ((in & trigger_combo) == 0) && (trigger_combo != 0);
  endfunction

  task check_ec_rst_inactive(int max_cycle);
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(0, max_cycle));
    `DV_CHECK_EQ(cfg.vif.ec_rst_l_out, 1)
  endtask

  task config_register();
    // TODO: Add other set of combo registers
    // Enable input keys to trigger the combo
    csr_wr(ral.com_sel_ctl[0], trigger_combo);
    `uvm_info(`gfn, $sformatf("Write data of com_sel_ctl_0 register:0x%0h",
                               trigger_combo), UVM_LOW)

    // Set the duration for combo to pressed
    csr_wr(ral.com_det_ctl[0], set_duration);
    `uvm_info(`gfn, $sformatf("Write data of com_det_ctl_0 register:0x%0h",
                               set_duration), UVM_LOW);

    // Set the trigger action
    csr_wr(ral.com_out_ctl[0], set_action);
    `uvm_info(`gfn, $sformatf("Write data of com_out_ctl_0 register:0x%0h",
                               set_action), UVM_LOW);

    // Set the ec_rst_0 pulse width
    csr_wr(ral.ec_rst_ctl, set_pulse_width);
    `uvm_info(`gfn, $sformatf("Write data of ec_rst_ctl register:0x%0h",
                               set_pulse_width), UVM_LOW);

    // Set the key triggered debounce timer
    csr_wr(ral.key_intr_debounce_ctl, set_key_timer);
    `uvm_info(`gfn, $sformatf("Write data of key_intr_debounce_ctl register:0x%0h",
                               set_key_timer), UVM_LOW);
  endtask

  task body();
    uvm_reg_data_t rdata;
    bit int_act_set, bat_act_set, ec_act_set, rst_act_set;
    bit triggered;

    // Enable interrupt
    ral.intr_enable.set(1);
    csr_update(ral.intr_enable);

    `uvm_info(`gfn, "Starting the body from combo detect", UVM_LOW)

    // Disable the override function
    ral.pin_out_ctl.ec_rst_l.set(0);
    csr_update(ral.pin_out_ctl);

    config_register();
    monitor_ec_rst_low(set_pulse_width);

    // It takes 2-3 clock cycles to sync the register values
    cfg.clk_aon_rst_vif.wait_clks(3);

    repeat (num_trans) begin
      repeat ($urandom_range(1,5)) begin
        // Trigger the input pins
        cfg.clk_aon_rst_vif.wait_clks(1);
        cfg.vif.randomize_input();
      end

      // Wait for debounce + detect timer
      cfg.clk_aon_rst_vif.wait_clks(cycles+2);

      // Latch the trigger value before resetting the input pins
      triggered = get_combo_trigger();
      // Set the inputs back to inactive to avoid its affect in next iterations
      cfg.vif.pwrb_in = 1;
      cfg.vif.key0_in = 1;
      cfg.vif.key1_in = 1;
      cfg.vif.key2_in = 1;
      cfg.vif.ac_present = 1;

      `uvm_info(`gfn, $sformatf("Value of cycles:%0h", cycles), UVM_LOW)

      if (cycles < (set_duration + set_key_timer) || !triggered) begin
        // Check there is no interrupt if we wait for
        // cycles < debounce time + detect time
        cfg.clk_aon_rst_vif.wait_clks(1);
        check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(0));
        `DV_CHECK_EQ(cfg.vif.bat_disable, 0);
        `DV_CHECK_EQ(cfg.vif.sysrst_ctrl_rst_req, 0);
        check_ec_rst_inactive(set_pulse_width);
        `DV_CHECK_EQ(cfg.vif.ec_rst_l_out, 1);
      end else begin
        // Check if the interrupt has raised
        // NOTE: The interrupt will only raise if the interrupt
        // combo action is set
        int_act_set = get_field_val(ral.com_out_ctl[0].interrupt, set_action);
        bat_act_set = get_field_val(ral.com_out_ctl[0].bat_disable, set_action);
        ec_act_set = get_field_val(ral.com_out_ctl[0].ec_rst, set_action);
        rst_act_set = get_field_val(ral.com_out_ctl[0].rst_req, set_action);

        cfg.clk_aon_rst_vif.wait_clks(1);
        if (int_act_set == 1) begin
          check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(1));

          // Write to clear the interrupt
          csr_wr(ral.combo_intr_status, 'h1);

          cfg.clk_aon_rst_vif.wait_clks(20);
          // check if the interrupt is cleared
          csr_rd_check(ral.combo_intr_status, .compare_value(0));
        end else begin
          check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(0));
        end

        // If bat_disable trigger action is set then check if there is a transition
        // on cio_bat_disable_o signal
        if (bat_act_set == 1) begin
          `DV_CHECK_EQ(cfg.vif.bat_disable, 1);
        end else begin
          `DV_CHECK_EQ(cfg.vif.bat_disable, 0);
        end

        // If reset req trigger action is set then check if there is a event
        // on aon_sysrst_ctrl_rst_req_o pin
        if (rst_act_set == 1) begin
          `DV_CHECK_EQ(cfg.vif.sysrst_ctrl_rst_req, 1);
        end else begin
          `DV_CHECK_EQ(cfg.vif.sysrst_ctrl_rst_req, 0);
        end

        if (ec_act_set == 1) begin
          monitor_ec_rst_low(set_pulse_width);
        end else begin
          check_ec_rst_inactive(set_pulse_width);
          `DV_CHECK_EQ(cfg.vif.ec_rst_l_out, 0);
        end

        if (bat_act_set == 1 || rst_act_set == 1) begin
         cfg.clk_aon_rst_vif.apply_reset();
         // apply_reset will set the registers to their default values
         // wait for sometime and reconfigure the registers for next iteration
         cfg.clk_aon_rst_vif.wait_clks(10);
         config_register();
        end
        cfg.clk_aon_rst_vif.wait_clks(10);
      end
    end
  endtask : body

endclass : sysrst_ctrl_combo_detect_vseq

