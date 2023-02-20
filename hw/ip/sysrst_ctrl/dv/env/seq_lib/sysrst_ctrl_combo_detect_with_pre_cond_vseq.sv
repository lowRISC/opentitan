// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will write a random values to combo detect registers including
// precondition settings and check for the combo detect interrupt.
class sysrst_ctrl_combo_detect_with_pre_cond_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_combo_detect_with_pre_cond_vseq)

  `uvm_object_new
  rand uvm_reg_data_t set_action[4];
  rand bit[4:0] trigger_combo[4], trigger_combo_precondition[4];
  rand uint16_t set_duration[4], set_duration_precondition[4];
  rand uint16_t cycles, cycles_precondition;
  rand uint16_t set_pulse_width, set_key_timer, num_trans_combo_detect;

  constraint num_trans_c {num_trans == 80;}

  constraint num_trans_combo_detect_c {num_trans_combo_detect == 20;}

  constraint set_duration_precondition_c {
    foreach (set_duration_precondition[i]) {
      set_duration_precondition[i] dist {
        [10:100]  :/ 95,
        [101:300] :/ 5
      };
    }
  }

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
      cycles > set_duration[i] + set_key_timer;
    }
  }

  constraint cycles_precondition_c {
    foreach (set_duration_precondition[i]) {
      solve set_duration_precondition[i] before cycles_precondition;
      cycles_precondition dist {
        [1 : (set_duration_precondition[i] + set_key_timer) - 2] :/ 20,
        [(set_duration_precondition[i]) + 5 : (set_duration_precondition[i] + set_key_timer) * 2]   :/ 80
      };
      // Don't fall into this uncerntain period.
      !(cycles_precondition inside {[(set_duration_precondition[i] + set_key_timer) - 1 :
                        (set_duration_precondition[i] + set_key_timer) + 5]});
    }
  }

  // check for a input singal transition that triggers the combo detection logic
  function bit get_combo_trigger(int index, bit[4:0] combo_input_prev);
      logic [4:0] in;
      in[0] = cfg.vif.key0_in;
      in[1] = cfg.vif.key1_in;
      in[2] = cfg.vif.key2_in;
      in[3] = cfg.vif.pwrb_in;
      in[4] = cfg.vif.ac_present;
      `uvm_info(`gfn, $sformatf("DETECTION: i:%0d, in: %5b prev_in: %5b sel:%5b", index, in,
                       combo_input_prev, trigger_combo[index]), UVM_LOW)
      // check for signal transition
      return  (((combo_input_prev & ~in) & trigger_combo[index]) == trigger_combo[index]) &&
                   (trigger_combo[index] != 0);
  endfunction

  // check for a input combination that triggers the combo precondition logic
  function bit get_combo_precondition_trigger(int index);
      logic [4:0] in;
      in[0] = cfg.vif.key0_in;
      in[1] = cfg.vif.key1_in;
      in[2] = cfg.vif.key2_in;
      in[3] = cfg.vif.pwrb_in;
      in[4] = cfg.vif.ac_present;
      `uvm_info(`gfn, $sformatf("PRECONDITION: i:%0d, in: %5b prev_in:%5b sel:%5b", index, in,
                                 combo_input_prev, trigger_combo_precondition[index]),
                                 UVM_LOW)
      return  ((in & trigger_combo_precondition[index]) == 0);
  endfunction

  task check_ec_rst_inactive(int max_cycle);
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(0, max_cycle));
    `DV_CHECK_EQ(cfg.vif.ec_rst_l_out, 1)
  endtask

  // restrict trigger combo and precondition settings such that the probability of combo
  // precondition and combo detect selecting the same key is 2%
  function void post_randomize();
    foreach(trigger_combo[i])
    begin
      if(trigger_combo[i] & trigger_combo_precondition[i] > 0)
      begin
         if($urandom_range(0,100)>2)
         begin
            uint16_t bit_mask = trigger_combo[i] & trigger_combo_precondition[i];
            trigger_combo_precondition[i] &= (~bit_mask);
         end
      end
    end
  endfunction


  task config_register();
    // select the inputs for precondition
    foreach (ral.com_pre_sel_ctl[i]) csr_wr(ral.com_pre_sel_ctl[i], trigger_combo_precondition[i]);

    // Set the duration for precondition keys to pressed
    foreach (ral.com_pre_det_ctl[i]) csr_wr(ral.com_pre_det_ctl[i], set_duration_precondition[i]);

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

    `uvm_info(`gfn, "Starting the body from combo detect with precondition", UVM_LOW)

    // start sequence by releaseing ec_rst_l_o. post reset ec_rst_l_o remains asserted,
    // and must be deasserted. This is to make sure during test, the H->L and L->H transitions
    // of ec_rst_l_o can be observed
    release_ec_rst_l_o();
    // reset combo logic input
    reset_combo_inputs();
    // configure combo logic registers
    config_register();
    // print combo detection and precondition settings
    for(int i=0;i<4;i++) begin
      `uvm_info(`gfn,$sformatf("COM_PRE_DET_CTL_%0d : %0d", i, set_duration_precondition[i]),
                               UVM_LOW)
      `uvm_info(`gfn,$sformatf("COM_DET_CTL_%0d     : %0d", i, set_duration[i]), UVM_LOW)
      `uvm_info(`gfn,$sformatf("COM_PRE_SEL_CTL_%0d : 0x%0x", i, trigger_combo_precondition[i]),
                                UVM_LOW)
      `uvm_info(`gfn,$sformatf("COM_SEL_CTL_%0d     : 0x%0x", i, trigger_combo[i]),
                                UVM_LOW)
    end
    `uvm_info(`gfn, $sformatf("Value of cycles_precondition:%0d", cycles_precondition), UVM_LOW)
    `uvm_info(`gfn, $sformatf("Value of cycles:%0d", cycles), UVM_LOW)
    // It takes 2-3 clock cycles to sync the register values
    cfg.clk_aon_rst_vif.wait_clks(3);
    repeat(num_trans)
    begin : main_block
      bit precond_detected_for_one_block = 1'b0;
      bit  [3:0] precondition_detected = '{4{1'b0}};
      cfg.vif.randomize_combo_input();
      // Wait for debounce + detect timer
      cfg.clk_aon_rst_vif.wait_clks(cycles_precondition);
      for(int i=0;i<4;i++) begin
         if(cycles_precondition >(set_duration_precondition[i]+ set_key_timer) &&
              get_combo_precondition_trigger(i)) begin
           precondition_detected[i] = (trigger_combo[i] & trigger_combo_precondition[i])==0;
           precond_detected_for_one_block |= precondition_detected[i];
         end
      end
      if(precond_detected_for_one_block)
      begin: combo_detect_block
        bit triggered[4];
        uvm_reg_data_t       rdata;
        uint16_t [3:0]       get_duration;
        uvm_reg_data_t [3:0] get_action;
        bit [3:0]            combo_detected;
        bit [4:0]             combo_precondition_mask=4'h0;
        bit [4:0]             get_trigger_combo[4];
        bit [4:0]             get_trigger_combo_pre[4];
        bit [4:0]             combo_input_prev;
        foreach(precondition_detected[i]) begin
          if(precondition_detected[i])
            `uvm_info(`gfn, $sformatf("valid precondition detected for combo channel: %0d",i),
                                    UVM_LOW)
        end
        // update combo_precondition_mask
        for(int i=0;i<4;i++) begin
          if(precondition_detected[i]) combo_precondition_mask |= trigger_combo[i];
        end

        while(precondition_detected >0 && (combo_detected != precondition_detected) &&
               num_trans_combo_detect>0)  begin:combo_action_check
          bit bat_act_triggered, ec_act_triggered, rst_act_triggered;
          bit [3:0] intr_actions, intr_actions_pre_reset;
          int ec_act_occur_cyc = 0;
          combo_input_prev = get_combo_input();
          // randomize combo logic inputs except the ones asserted for precondition
          cfg.vif.randomize_combo_input(combo_precondition_mask);

          // Wait for debounce + detect timer
          cfg.clk_aon_rst_vif.wait_clks(cycles);

          // Latch the trigger
          foreach (triggered[i]) triggered[i] = get_combo_trigger(i, combo_input_prev)
                                                  && precondition_detected[i];

          foreach (intr_actions_pre_reset[i]) begin
            intr_actions_pre_reset[i] = get_field_val(ral.com_out_ctl[i].interrupt, get_action[i]);
          end
          foreach (ral.com_det_ctl[i]) csr_rd(ral.com_det_ctl[i], get_duration[i]);
          foreach (ral.com_out_ctl[i]) csr_rd(ral.com_out_ctl[i], get_action[i]);
          foreach (ral.com_sel_ctl[i]) csr_rd(ral.com_sel_ctl[i], get_trigger_combo[i]);
          foreach (ral.com_sel_ctl[i]) csr_rd(ral.com_pre_sel_ctl[i], get_trigger_combo_pre[i]);

          // Sample the combo_intr_status covergroup to capture the trigger combo inputs
          // before resetting the combo inputs.
          if (cfg.en_cov) begin
            for(int i=0;i<4;i++) begin
              cov.combo_detect_action[i].sysrst_ctrl_combo_detect_action_cg.sample(
                              bat_act_triggered,
                              intr_actions[i],
                              ec_act_triggered,
                              rst_act_triggered,
                              get_field_val(ral.com_sel_ctl[i].key0_in_sel, get_trigger_combo[i]),
                              get_field_val(ral.com_sel_ctl[i].key1_in_sel, get_trigger_combo[i]),
                              get_field_val(ral.com_sel_ctl[i].key2_in_sel, get_trigger_combo[i]),
                              get_field_val(ral.com_sel_ctl[i].pwrb_in_sel, get_trigger_combo[i]),
                              get_field_val(ral.com_sel_ctl[i].ac_present_sel,get_trigger_combo[i]),
                              get_field_val(ral.com_pre_sel_ctl[i].key0_in_sel,
                                                               get_trigger_combo_pre[i]),
                              get_field_val(ral.com_pre_sel_ctl[i].key1_in_sel,
                                                               get_trigger_combo_pre[i]),
                              get_field_val(ral.com_pre_sel_ctl[i].key2_in_sel,
                                                               get_trigger_combo_pre[i]),
                              get_field_val(ral.com_pre_sel_ctl[i].pwrb_in_sel,
                                                               get_trigger_combo_pre[i]),
                              get_field_val(ral.com_pre_sel_ctl[i].ac_present_sel,
                                                               get_trigger_combo_pre[i]));
            end
          end

          foreach(triggered[i]) begin
            if(triggered[i])
              `uvm_info(`gfn, $sformatf("valid combo input transition detected for channel :%0d",i),
                                          UVM_LOW)
          end

          // Check if the interrupt has raised.
          // NOTE: The interrupt will only raise if the interrupt combo action is set.
          for (int i = 0; i <= 3; i++) begin
            if (cycles > (get_duration[i] + set_key_timer) && triggered[i])
            begin
              intr_actions[i] = get_field_val(ral.com_out_ctl[i].interrupt, get_action[i]);
              bat_act_triggered |= get_field_val(ral.com_out_ctl[i].bat_disable, get_action[i]);
              ec_act_triggered |= get_field_val(ral.com_out_ctl[i].ec_rst, get_action[i]);
              rst_act_triggered |= get_field_val(ral.com_out_ctl[i].rst_req, get_action[i]);

              if (get_field_val(ral.com_out_ctl[i].ec_rst, get_action[i])) begin
                ec_act_triggered = 1;
                combo_detected[i]=1;
                // Record which cycle the ec_rst occurs, just need to know the last combo
                // that triggers the ec_rst
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

          if (intr_actions) begin
            check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(1));

            // Write to clear the interrupt.
            csr_wr(ral.combo_intr_status, rdata);

            cfg.clk_aon_rst_vif.wait_clks(5);
            // Check if the interrupt is cleared.
            csr_rd_check(ral.combo_intr_status, .compare_value(0));

          end else begin
            check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(0));
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
            // Delay to avoid race condition when sending item and checking no item after
            // reset occur at the same time.
            #1ps;
            // release ec_rst_l_o after reset
            release_ec_rst_l_o();
            // Apply_resets_concurrently will set the registers to their default values,
            // wait for sometime and reconfigure the registers for next iteration.
            config_register();
          end
            cfg.clk_aon_rst_vif.wait_clks(10);
            num_trans_combo_detect--;
        end : combo_action_check
      end: combo_detect_block
      // Reset combo inputs after iteration
      reset_combo_inputs();
      cfg.clk_aon_rst_vif.wait_clks(2);
    end: main_block
  endtask : body

endclass : sysrst_ctrl_combo_detect_with_pre_cond_vseq
