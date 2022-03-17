// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will write a random values to combo detect registers
// and check for the combo detect interrupt
class sysrst_ctrl_combo_detect_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_combo_detect_vseq)

  `uvm_object_new
  rand uvm_reg_data_t set_action[4];
  rand bit[4:0] trigger_combo[4];
  rand uint16_t set_duration[4];
  rand uint16_t set_pulse_width, set_key_timer;
  rand uint16_t cycles;

  constraint num_trans_c {num_trans == 2;}

  constraint set_duration_c {
    set_duration[0] dist {
      [10:100] :/ 95,
      [101:$]   :/ 5
    };
    set_duration[1] dist {
      [10:100] :/ 95,
      [101:$]   :/ 5
    };
    set_duration[2] dist {
      [10:100] :/ 95,
      [101:$]   :/ 5
    };
    set_duration[3] dist {
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
      [1 : (set_duration[0] + set_key_timer) - 2] :/ 20,
      [(set_duration[0] + set_key_timer) + 5 : (set_duration[0] + set_key_timer) * 2]   :/ 80
    };
    cycles dist {
      [1 : (set_duration[1] + set_key_timer) - 2] :/ 20,
      [(set_duration[1] + set_key_timer) + 5 : (set_duration[1] + set_key_timer) * 2]   :/ 80
    };
    cycles dist {
      [1 : (set_duration[2] + set_key_timer) - 2] :/ 20,
      [(set_duration[2] + set_key_timer) + 5 : (set_duration[2] + set_key_timer) * 2]   :/ 80
    };
    cycles dist {
      [1 : (set_duration[3] + set_key_timer) - 2] :/ 20,
      [(set_duration[3] + set_key_timer) + 5 : (set_duration[3] + set_key_timer) * 2]   :/ 80
    };
  }

  function bit get_combo_trigger(int index);
      logic [4:0] in;
      in[0] = cfg.vif.key0_in;
      in[1] = cfg.vif.key1_in;
      in[2] = cfg.vif.key2_in;
      in[3] = cfg.vif.pwrb_in;
      in[4] = cfg.vif.ac_present;
      return  ((in & trigger_combo[index]) == 0) && (trigger_combo[index] != 0);
  endfunction

  task check_ec_rst_inactive(int max_cycle);
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(0, max_cycle));
    `DV_CHECK_EQ(cfg.vif.ec_rst_l_out, 1)
  endtask

  task config_register();
    // Select the inputs for the combo
    foreach (ral.com_sel_ctl[i]) csr_wr(ral.com_sel_ctl[i], trigger_combo[i]);

    // Set the duration for combo to pressed
    foreach (ral.com_det_ctl[i]) csr_wr(ral.com_det_ctl[i], set_duration[i]);

    // Set the trigger action
    foreach (ral.com_out_ctl[i]) csr_wr(ral.com_out_ctl[i], set_action[i]);

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
    bit [3:0] int_act_set;
    bit [3:0] bat_act_set;
    bit [3:0] ec_act_set;
    bit [3:0] rst_act_set;
    bit triggered[4];
    uint16_t [3:0] set_duration;

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
      cfg.clk_aon_rst_vif.wait_clks(cycles);

      // Latch the trigger value before resetting the input pins
      foreach (triggered[i]) triggered[i] = get_combo_trigger(i);

      // Set the inputs back to inactive to avoid its affect in next iterations
      cfg.vif.pwrb_in = 1;
      cfg.vif.key0_in = 1;
      cfg.vif.key1_in = 1;
      cfg.vif.key2_in = 1;
      cfg.vif.ac_present = 1;

      `uvm_info(`gfn, $sformatf("Value of cycles:%0h", cycles), UVM_LOW)
      for (int i = 0; i <= 3; i++) begin
        if (cycles < (set_duration[i] + set_key_timer) || !triggered[i]) begin
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
          int_act_set[i] = get_field_val(ral.com_out_ctl[i].interrupt, set_action[i]);
          bat_act_set[i] = get_field_val(ral.com_out_ctl[i].bat_disable, set_action[i]);
          ec_act_set[i] = get_field_val(ral.com_out_ctl[i].ec_rst, set_action[i]);
          rst_act_set[i] = get_field_val(ral.com_out_ctl[i].rst_req, set_action[i]);

          cfg.clk_aon_rst_vif.wait_clks(1);
          if (int_act_set[i]) begin
            check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(1));

            // Read the status register
            csr_rd(ral.combo_intr_status, rdata);
            `DV_CHECK_EQ(rdata[i], 'h1)

            // Write to clear the interrupt
            csr_wr(ral.combo_intr_status, rdata);

            cfg.clk_aon_rst_vif.wait_clks(20);
            // check if the interrupt is cleared
            csr_rd_check(ral.combo_intr_status, .compare_value(0));
          end else begin
            check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(0));
          end

          // If bat_disable trigger action is set then check if there is a transition
          // on cio_bat_disable_o signal
          if (bat_act_set[i]) begin
            `DV_CHECK_EQ(cfg.vif.bat_disable, 1);
          end else begin
            `DV_CHECK_EQ(cfg.vif.bat_disable, 0);
          end

          // If reset req trigger action is set then check if there is a event
          // on aon_sysrst_ctrl_rst_req_o pin
          if (rst_act_set[i]) begin
           `DV_CHECK_EQ(cfg.vif.sysrst_ctrl_rst_req, 1);
          end else begin
            `DV_CHECK_EQ(cfg.vif.sysrst_ctrl_rst_req, 0);
          end

          if (ec_act_set[i]) begin
            monitor_ec_rst_low(set_pulse_width);
          end else begin
            check_ec_rst_inactive(set_pulse_width);
            `DV_CHECK_EQ(cfg.vif.ec_rst_l_out, 1);
          end

          if (bat_act_set[i] == 1 || rst_act_set[i] == 1) begin
           cfg.clk_aon_rst_vif.apply_reset();
           // apply_reset will set the registers to their default values
           // wait for sometime and reconfigure the registers for next iteration
           config_register();
          end
          cfg.clk_aon_rst_vif.wait_clks(10);
        end
      end
     end
  endtask : body

endclass : sysrst_ctrl_combo_detect_vseq

