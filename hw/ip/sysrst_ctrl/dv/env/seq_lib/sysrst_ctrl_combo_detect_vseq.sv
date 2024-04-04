// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will write a random values to combo detect registers
// and check for the combo detect interrupt.
class sysrst_ctrl_combo_detect_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_combo_detect_vseq)

  `uvm_object_new
  rand uvm_reg_data_t set_action[4];
  rand bit[4:0] trigger_combo[4];
  rand uint16_t set_duration[4];
  rand uint16_t set_pulse_width, set_key_timer;
  rand uint16_t cycles;

  constraint num_trans_c {num_trans == 20;}

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
      [10:100]  :/ 95,
      [101:300] :/ 5
    };

   // ec_rst will trigger a pulse, we check all the action after 4 set_duration are done
   // make the set_pulse_width larger than any of the duration, so that we can still check it's
   // value.
   foreach (set_duration[i]) {
     if (cycles > set_duration[i] + set_key_timer) {
       set_pulse_width > cycles - (set_duration[i] + set_key_timer);
     }
   }
  }

  constraint set_key_timer_c {
    set_key_timer dist {
      [10:100]  :/ 95,
      [101:300] :/ 5
    };
  }

  constraint cycles_c {
    foreach (set_duration[i]) {
      cycles dist {
        [1 : (set_duration[i] + set_key_timer) - 2] :/ 20,
        [(set_duration[i] + set_key_timer) + 5 : (set_duration[i] + set_key_timer) * 2]   :/ 80
      };
      // Don't fall into this uncerntain period.
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

  task body();
    uvm_reg_data_t rdata;
    bit triggered[4];
    uint16_t [3:0] set_duration;
    uint16_t [3:0] get_duration;
    uvm_reg_data_t [3:0] get_action;
    bit[4:0] get_trigger_combo[4];
    bit [4:0] get_trigger_combo_pre[4];

    `uvm_info(`gfn, "Starting the body from combo detect", UVM_LOW)

    // post reset ec_rst_l_o remains asserted, and must be deasserted
    // This is to make sure during test, the H->L and L->H transitions of ec_rst_l_o can be observed
    release_ec_rst_l_o();

    reset_combo_inputs();
    config_register();

    // It takes 2-3 clock cycles to sync the register values
    cfg.clk_aon_rst_vif.wait_clks(3);

    repeat (num_trans) begin
      bit bat_act_triggered, ec_act_triggered, rst_act_triggered;
      bit current_bat_act, current_ec_act, current_rst_act;
      bit [3:0] intr_actions, intr_actions_pre_reset;
      int ec_act_occur_cyc = 0;
      repeat ($urandom_range(1, 2)) begin
        // Trigger the input pins
        cfg.clk_aon_rst_vif.wait_clks(1);
        cfg.vif.randomize_combo_input();
      end

      // Wait for debounce + detect timer
      cfg.clk_aon_rst_vif.wait_clks(cycles);

      // Latch the trigger value before resetting the input pins
      foreach (triggered[i]) triggered[i] = get_combo_trigger(i);

      foreach (intr_actions_pre_reset[i]) begin
        intr_actions_pre_reset[i] = get_field_val(ral.com_out_ctl[i].interrupt, get_action[i]);
      end

      // Sample the combo_intr_status covergroup to capture the trigger combo inputs
      // before resetting the combo inputs.
      if (cfg.en_cov) begin
        cov.combo_intr_status.sysrst_ctrl_combo_intr_status_cg.sample(
            get_field_val(ral.combo_intr_status.combo0_h2l, rdata),
            get_field_val(ral.combo_intr_status.combo1_h2l, rdata),
            get_field_val(ral.combo_intr_status.combo2_h2l, rdata),
            get_field_val(ral.combo_intr_status.combo3_h2l, rdata),
            cfg.vif.key0_in,
            cfg.vif.key1_in,
            cfg.vif.key2_in,
            cfg.vif.pwrb_in,
            cfg.vif.ac_present,
            intr_actions_pre_reset
        );
      end

      reset_combo_inputs();

      `uvm_info(`gfn, $sformatf("Value of cycles:%0d", cycles), UVM_LOW)
      foreach (ral.com_det_ctl[i]) csr_rd(ral.com_det_ctl[i], get_duration[i]);
      foreach (ral.com_out_ctl[i]) csr_rd(ral.com_out_ctl[i], get_action[i]);
      foreach (ral.com_sel_ctl[i]) csr_rd(ral.com_sel_ctl[i], get_trigger_combo[i]);
      foreach (ral.com_sel_ctl[i]) csr_rd(ral.com_pre_sel_ctl[i], get_trigger_combo_pre[i]);

      // Check if the interrupt has raised.
      // NOTE: The interrupt will only raise if the interrupt combo action is set.
      for (int i = 0; i <= 3; i++) begin
        if (cycles > (get_duration[i] + set_key_timer) && triggered[i]) begin
          intr_actions[i]    = get_field_val(ral.com_out_ctl[i].interrupt, get_action[i]);
          current_bat_act    = get_field_val(ral.com_out_ctl[i].bat_disable, get_action[i]);
          current_ec_act     = get_field_val(ral.com_out_ctl[i].ec_rst, get_action[i]);
          current_rst_act    = get_field_val(ral.com_out_ctl[i].rst_req, get_action[i]);
          bat_act_triggered |= current_bat_act;
          ec_act_triggered  |= current_ec_act;
          rst_act_triggered |= current_rst_act;

          if (cfg.en_cov) begin
            cov.combo_detect_action[i].sysrst_ctrl_combo_detect_action_cg.sample(
              current_bat_act,
              intr_actions[i],
              current_ec_act,
              current_rst_act,
              get_field_val(ral.com_sel_ctl[i].key0_in_sel, get_trigger_combo[i]),
              get_field_val(ral.com_sel_ctl[i].key1_in_sel, get_trigger_combo[i]),
              get_field_val(ral.com_sel_ctl[i].key2_in_sel, get_trigger_combo[i]),
              get_field_val(ral.com_sel_ctl[i].pwrb_in_sel, get_trigger_combo[i]),
              get_field_val(ral.com_sel_ctl[i].ac_present_sel, get_trigger_combo[i]),
              get_field_val(ral.com_pre_sel_ctl[i].key0_in_sel, get_trigger_combo_pre[i]),
              get_field_val(ral.com_pre_sel_ctl[i].key1_in_sel, get_trigger_combo_pre[i]),
              get_field_val(ral.com_pre_sel_ctl[i].key2_in_sel, get_trigger_combo_pre[i]),
              get_field_val(ral.com_pre_sel_ctl[i].pwrb_in_sel, get_trigger_combo_pre[i]),
              get_field_val(ral.com_pre_sel_ctl[i].ac_present_sel, get_trigger_combo_pre[i])
            );
            cov.combo_key_combinations.sysrst_ctrl_combo_key_combinations_cg.sample(
              current_bat_act,
              intr_actions[i],
              current_ec_act,
              current_rst_act,
              get_field_val(ral.com_sel_ctl[i].key0_in_sel, get_trigger_combo[i]),
              get_field_val(ral.com_sel_ctl[i].key1_in_sel, get_trigger_combo[i]),
              get_field_val(ral.com_sel_ctl[i].key2_in_sel, get_trigger_combo[i]),
              get_field_val(ral.com_sel_ctl[i].pwrb_in_sel, get_trigger_combo[i]),
              get_field_val(ral.com_sel_ctl[i].ac_present_sel, get_trigger_combo[i]),
              get_field_val(ral.com_pre_sel_ctl[i].key0_in_sel, get_trigger_combo_pre[i]),
              get_field_val(ral.com_pre_sel_ctl[i].key1_in_sel, get_trigger_combo_pre[i]),
              get_field_val(ral.com_pre_sel_ctl[i].key2_in_sel, get_trigger_combo_pre[i]),
              get_field_val(ral.com_pre_sel_ctl[i].pwrb_in_sel, get_trigger_combo_pre[i]),
              get_field_val(ral.com_pre_sel_ctl[i].ac_present_sel, get_trigger_combo_pre[i])
            );
          end

          if (get_field_val(ral.com_out_ctl[i].ec_rst, get_action[i])) begin
            ec_act_triggered = 1;
            // Record which cycle the ec_rst occurs, just need to know the last combo that triggers
            // the ec_rst
            ec_act_occur_cyc = max2(ec_act_occur_cyc, get_duration[i] + set_key_timer);
          end
        end
      end

      if (ec_act_triggered) begin
        // We don't check ec_rst_pulse right after it occurs. past_cycles indicates how many
        // cycles the pulse has been active.
        // -2 is because cross clock domaim make take ~2 cycles.
        int past_cycles = cycles - ec_act_occur_cyc - 2;
        monitor_ec_rst_low(set_pulse_width - past_cycles);
      end else begin
        check_ec_rst_inactive(set_pulse_width);
        `DV_CHECK_EQ(cfg.vif.ec_rst_l_out, 1);
      end

      cfg.clk_aon_rst_vif.wait_clks(1);
      csr_rd(ral.combo_intr_status, rdata);
      `DV_CHECK_EQ(rdata, intr_actions)

      // If intr_actions is set then check if there is a transition
      // on wkup_req_o signal
      if (intr_actions) begin
        `DV_CHECK_EQ(cfg.vif.wkup_req, 1);
      end else begin
        `DV_CHECK_EQ(cfg.vif.wkup_req, 0);
      end

      if (intr_actions) begin
        check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(1));

        // Write to clear the interrupt.
        csr_wr(ral.combo_intr_status, rdata);

        cfg.clk_aon_rst_vif.wait_clks(5);
        // Check if the interrupt is cleared.
        csr_rd_check(ral.combo_intr_status, .compare_value(0));

        // Sample the combo intr status covergroup.
        // The combo_intr_status get updated only when the interrupt action is triggered.
        if (cfg.en_cov) begin
          cov.combo_intr_status.sysrst_ctrl_combo_intr_status_cg.sample(
            get_field_val(ral.combo_intr_status.combo0_h2l, rdata),
            get_field_val(ral.combo_intr_status.combo1_h2l, rdata),
            get_field_val(ral.combo_intr_status.combo2_h2l, rdata),
            get_field_val(ral.combo_intr_status.combo3_h2l, rdata),
            cfg.vif.key0_in,
            cfg.vif.key1_in,
            cfg.vif.key2_in,
            cfg.vif.pwrb_in,
            cfg.vif.ac_present,
            intr_actions);
        end
        // Check wkup_status register
        csr_rd(ral.wkup_status, rdata);
        if(!get_field_val(ral.wkup_status.wakeup_sts, rdata)) begin
          `uvm_error(`gfn, "wkup_status.wakeup_sts set to 0")
        end
        // Write to clear wkup_req status, register is of type rw1c
        csr_wr(ral.wkup_status, uvm_reg_data_t'('d1));
        cfg.clk_aon_rst_vif.wait_clks(5);
        // Check if status bit is cleared
        csr_rd_check(ral.wkup_status, .compare_value(0));
      end else begin
        check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(0));
        csr_rd_check(ral.wkup_status, .compare_value(0));
      end

      // If bat_disable trigger action is set then check if there is a transition
      // on cio_bat_disable_o signal.
      if (bat_act_triggered) begin
        `DV_CHECK_EQ(cfg.vif.bat_disable, 1);
      end else begin
        `DV_CHECK_EQ(cfg.vif.bat_disable, 0);
      end

      // If reset req trigger action is set then check if there is a event
      // on aon_rst_req_o pin.
      if (rst_act_triggered) begin
        `DV_CHECK_EQ(cfg.vif.rst_req, 1);
      end else begin
        `DV_CHECK_EQ(cfg.vif.rst_req, 0);
      end

      if (bat_act_triggered || rst_act_triggered) begin
        apply_resets_concurrently();
        // Delay to avoid race condition when sending item and checking no item after reset occur
        // at the same time.
        #1ps;
        // release ec_rst_l_o after reset
        release_ec_rst_l_o();
        // Apply_resets_concurrently will set the registers to their default values,
        // wait for sometime and reconfigure the registers for next iteration.
        config_register();
      end
        cfg.clk_aon_rst_vif.wait_clks(10);
     end
  endtask : body

endclass : sysrst_ctrl_combo_detect_vseq
