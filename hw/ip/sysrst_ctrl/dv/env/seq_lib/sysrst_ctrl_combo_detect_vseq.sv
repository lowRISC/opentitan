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
    foreach (set_duration[i]) {
      set_duration[i] dist {
        [10:100]  :/ 95,
        [101:300] :/ 5
      };
    }
  }

  constraint set_pulse_width_c {
    set_pulse_width dist {
      [10:100] :/ 95,
      [101:300]   :/ 5
    };

   // ec_rst will trigger a pulse, we check all the action after 4 set_duration are done
   // make the set_pulse_width larger than any of the duration, so that we can still check it's
   // value
   foreach (set_duration[i]) {
     if (cycles > set_duration[i] + set_key_timer) {
       set_pulse_width > cycles - (set_duration[i] + set_key_timer);
     }
   }
  }

  constraint set_key_timer_c {
    set_key_timer dist {
      [10:100] :/ 95,
      [101:300]   :/ 5
    };
  }

  constraint cycles_c {
    foreach (set_duration[i]) {
      cycles dist {
        [1 : (set_duration[i] + set_key_timer) - 2] :/ 20,
        [(set_duration[i] + set_key_timer) + 5 : (set_duration[i] + set_key_timer) * 2]   :/ 80
      };
      // don't fall into this uncerntain period
      !(cycles inside {[(set_duration[i] + set_key_timer) - 1 :
                        (set_duration[i] + set_key_timer) + 5]});
    }
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
    // Disable the override function
    ral.pin_out_ctl.ec_rst_l.set(0);
    csr_update(ral.pin_out_ctl);

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

  function void reset_combo_inputs();
    // Set the inputs back to inactive to avoid its affect in next iterations
    cfg.vif.pwrb_in = 1;
    cfg.vif.key0_in = 1;
    cfg.vif.key1_in = 1;
    cfg.vif.key2_in = 1;
    cfg.vif.ac_present = 1;
  endfunction

  task body();
    uvm_reg_data_t rdata;
    bit triggered[4];
    uint16_t [3:0] set_duration;
    uint16_t [3:0] get_duration;
    uvm_reg_data_t [3:0] get_action;
    bit[4:0] get_trigger_combo[4];

    `uvm_info(`gfn, "Starting the body from combo detect", UVM_LOW)

    reset_combo_inputs();
    config_register();

    monitor_ec_rst_low(set_pulse_width);

    // It takes 2-3 clock cycles to sync the register values
    cfg.clk_aon_rst_vif.wait_clks(3);

    repeat (num_trans) begin
      bit bat_act_triggered, ec_act_triggered, rst_act_triggered;
      bit [3:0] intr_actions;
      int ec_act_occur_cyc = cycles;
      repeat ($urandom_range(1, 2)) begin
        // Trigger the input pins
        cfg.clk_aon_rst_vif.wait_clks(1);
        cfg.vif.randomize_combo_input();
      end

      // Wait for debounce + detect timer
      cfg.clk_aon_rst_vif.wait_clks(cycles);

      // Latch the trigger value before resetting the input pins
      foreach (triggered[i]) triggered[i] = get_combo_trigger(i);

      reset_combo_inputs();

      `uvm_info(`gfn, $sformatf("Value of cycles:%0d", cycles), UVM_LOW)
      foreach (ral.com_det_ctl[i]) csr_rd(ral.com_det_ctl[i], get_duration[i]);
      foreach (ral.com_out_ctl[i]) csr_rd(ral.com_out_ctl[i], get_action[i]);
      foreach (ral.com_sel_ctl[i]) csr_rd(ral.com_sel_ctl[i], get_trigger_combo[i]);

      // Check if the interrupt has raised
      // NOTE: The interrupt will only raise if the interrupt
      // combo action is set
      for (int i = 0; i <= 3; i++) begin
        if (cycles > (get_duration[i] + set_key_timer) && triggered[i]) begin
          intr_actions[i] = get_field_val(ral.com_out_ctl[i].interrupt, get_action[i]);
          bat_act_triggered |= get_field_val(ral.com_out_ctl[i].bat_disable, get_action[i]);
          ec_act_triggered |= get_field_val(ral.com_out_ctl[i].ec_rst, get_action[i]);
          rst_act_triggered |= get_field_val(ral.com_out_ctl[i].rst_req, get_action[i]);

          if (get_field_val(ral.com_out_ctl[i].ec_rst, get_action[i])) begin
            ec_act_triggered = 1;
            // record which cycle the ec_rst occurs
            ec_act_occur_cyc = min2(ec_act_occur_cyc, get_duration[i] + set_key_timer);
          end
        end
      end
      if (ec_act_triggered) begin
        // we don't check ec_rst_pulse right after it occurs. past_cycles indicates how many
        // cycles the pulse has been active
        // -2 is because cross clock domaim make take ~2 cycles
        int past_cycles = cycles - ec_act_occur_cyc - 2;
        monitor_ec_rst_low(set_pulse_width - past_cycles);
      end else begin
        check_ec_rst_inactive(set_pulse_width);
        `DV_CHECK_EQ(cfg.vif.ec_rst_l_out, 1);
      end

      cfg.clk_aon_rst_vif.wait_clks(1);
      csr_rd(ral.combo_intr_status, rdata);
      `DV_CHECK_EQ(rdata, intr_actions)

      if (intr_actions) begin
        check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(1));

        // Write to clear the interrupt
        csr_wr(ral.combo_intr_status, rdata);

        cfg.clk_aon_rst_vif.wait_clks(5);
        // check if the interrupt is cleared
        csr_rd_check(ral.combo_intr_status, .compare_value(0));
      end else begin
        check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(0));
      end

      // If bat_disable trigger action is set then check if there is a transition
      // on cio_bat_disable_o signal
      if (bat_act_triggered) begin
        `DV_CHECK_EQ(cfg.vif.bat_disable, 1);
      end else begin
        `DV_CHECK_EQ(cfg.vif.bat_disable, 0);
      end

      // If reset req trigger action is set then check if there is a event
      // on aon_sysrst_ctrl_rst_req_o pin
      if (rst_act_triggered) begin
        `DV_CHECK_EQ(cfg.vif.sysrst_ctrl_rst_req, 1);
      end else begin
        `DV_CHECK_EQ(cfg.vif.sysrst_ctrl_rst_req, 0);
      end


      if (bat_act_triggered || rst_act_triggered) begin
        apply_resets_concurrently();
        // delay to avoid race condition when sending item and checking no item after reset occur
        // at the same time
        #1ps;
        // apply_resets_concurrently will set the registers to their default values
        // wait for sometime and reconfigure the registers for next iteration
        config_register();
        monitor_ec_rst_low(set_pulse_width);
      end
        cfg.clk_aon_rst_vif.wait_clks(10);
     end
  endtask : body

endclass : sysrst_ctrl_combo_detect_vseq
