// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence asserts the inputs of sysrst_ctrl such that the
// key detection blocks transition from Debounce to Idle state
class sysrst_ctrl_feature_disable_vseq extends sysrst_ctrl_combo_detect_with_pre_cond_vseq;
  `uvm_object_utils(sysrst_ctrl_feature_disable_vseq)

  `uvm_object_new
  // ec_rst_l_o assertion time
  rand uint16_t set_pulse_width;
  // Key debounce timer
  rand uint16_t set_key_intr_timer;
  rand uvm_reg_data_t auto_block_out_ctl;
  rand uint16_t auto_block_debounce_ctl;
  // ULP debounce timer
  rand uint16_t ulp_debounce_ctl;

  constraint set_timer_c {set_key_intr_timer inside {[15 : 50]};}

  constraint trigger_combo_c {
    foreach (trigger_combo[i]) {
      !(trigger_combo_precondition[i] & trigger_combo[i]);
      trigger_combo[i] > 0;
    }
  }

  constraint trigger_combo_precondition_c {
    foreach (trigger_combo_precondition[i]) {
      trigger_combo_precondition[i] > 0;
      solve trigger_combo_precondition[i] before trigger_combo[i];
    }
  }

  // Set ec_rst_l_o assertion as combo output for all channels
  constraint set_action_c {
    foreach (set_action[i]) {
      set_action[i] == 4;
    }
  }

  constraint set_duration_c {
    foreach (set_duration[i]) {
      set_duration[i] inside {[10 : 50]};
    }
  }

  constraint set_duration_precondition_c {
    foreach (set_duration_precondition[i]) {
      set_duration_precondition[i] inside {[10 : 50]};
    }
  }

  constraint set_pulse_width_c {set_pulse_width inside {[50 : 100]};}

  constraint set_key_timer_c {set_key_timer inside {[15 : 50]};}

  constraint auto_block_debounce_ctl_c {auto_block_debounce_ctl inside {[15 : 50]};}

  constraint auto_block_out_ctl_c {
    // At least one input is auto-blocked
    auto_block_out_ctl & 'h3 > 0;
  }

  constraint ulp_debounce_time_c {ulp_debounce_ctl inside {[15 : 50]};}

  task combo_debounce_to_idle();
    // Reset Combo detect inputs
    reset_combo_inputs();
    release_ec_rst_l_o();
    // Set the ec_rst_0 pulse width
    csr_wr(ral.ec_rst_ctl, set_pulse_width);
    `uvm_info(`gfn, $sformatf("Write data of ec_rst_ctl register:%0d", set_pulse_width), UVM_LOW);

    // Set the key triggered debounce timer
    csr_wr(ral.key_intr_debounce_ctl, set_key_timer);
    `uvm_info(`gfn, $sformatf("Write data of key_intr_debounce_ctl register:%0d", set_key_timer),
              UVM_LOW);

    for (int i = 0; i < 4; i++) begin
      `uvm_info(`gfn, $sformatf("configuring combo channel %0d", i), UVM_LOW)
      // Scenario : Trigger precondition Debounce to Idle state via
      //            deassertion of inputs before debounce timer
      config_combo_register(i);
      // Set combo input
      reset_combo_inputs(~trigger_combo_precondition[i]);
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer - 10);
      // Deassert input signals before debounce timer
      reset_combo_inputs();
      cfg.clk_aon_rst_vif.wait_clks(15);

      // Scenario : Trigger precondition Debounce to Idle state via
      //            disabling precondition before debounce timer
      // Assert input signals to match predoncition selection
      reset_combo_inputs(~trigger_combo_precondition[i]);
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer - 10);
      // Disable precondition before debounce timer
      csr_wr(ral.com_pre_sel_ctl[i], 0);
      cfg.clk_aon_rst_vif.wait_clks(10);
      reset_combo_inputs();
      cfg.clk_aon_rst_vif.wait_clks(3);

      // Scenario : Trigger precondition Detect to Idle state via
      //            disabling precondition before detect timer
      // Assert input signals to match predoncition selection
      config_combo_register(i);
      reset_combo_inputs(~trigger_combo_precondition[i]);
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer + set_duration_precondition[i] - 10);
      // Disable precondition before detect timer
      csr_wr(ral.com_pre_sel_ctl[i], 0);
      cfg.clk_aon_rst_vif.wait_clks(10);
      reset_combo_inputs();
      cfg.clk_aon_rst_vif.wait_clks(3);

      // Scenario : Trigger precondition Detect to Idle state via
      //            deassertion of input signals
      // Assert input signals to match predoncition selection
      config_combo_register(i);
      reset_combo_inputs(~trigger_combo_precondition[i]);
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer + set_duration_precondition[i] - 10);
      // Disable precondition before detect timer
      reset_combo_inputs();
      cfg.clk_aon_rst_vif.wait_clks(15);

      // Scenario : Trigger combo detect Debounce to Idle state via
      //            deassertion of input signals before debounce timer
      // Set combo input to trigger precondition
      config_combo_register(i);
      reset_combo_inputs(~trigger_combo_precondition[i]);
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer + set_duration_precondition[i] + 10);
      // Set combo input to trigger combo detection
      reset_combo_inputs(~trigger_combo[i], ~trigger_combo_precondition[i]);
      // Wait for some time but dont exceed debounce time
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer - 10);
      // Deassert combo inputs before debounce timer
      reset_combo_inputs();
      cfg.clk_aon_rst_vif.wait_clks(10);

      // Scenario : Trigger combo detect Debounce to Idle state via
      //            disabling detection before debounce timer
      // Set combo input to trigger precondition
      reset_combo_inputs(~trigger_combo_precondition[i]);
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer + set_duration_precondition[i] + 10);
      // Set combo input to trigger combo detection
      reset_combo_inputs(~trigger_combo[i], ~trigger_combo_precondition[i]);
      // Wait for some time but dont exceed debounce time
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer - 10);
      // Disable combo detect before debounce timer
      csr_wr(ral.com_sel_ctl[i], 0);
      cfg.clk_aon_rst_vif.wait_clks(15);
      // Reset combo inputs
      reset_combo_inputs();
      cfg.clk_aon_rst_vif.wait_clks(10);

      // Scenario : Trigger combo Detect to Idle state via
      //            disabling detect before detect timer
      // Set combo input to trigger precondition
      config_combo_register(i);
      // Wait for 3 clock cycles to sync the register value
      cfg.clk_aon_rst_vif.wait_clks(3);
      reset_combo_inputs(~trigger_combo_precondition[i]);
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer + set_duration_precondition[i] + 10);
      // Set combo input to trigger combo detection
      reset_combo_inputs(~trigger_combo[i], ~trigger_combo_precondition[i]);
      // Wait for some time but dont exceed detect time
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer + set_duration[i] - 10);
      // Disable combo detect before detect timer
      csr_wr(ral.com_sel_ctl[i], 0);
      cfg.clk_aon_rst_vif.wait_clks(10);
      reset_combo_inputs();
      cfg.clk_aon_rst_vif.wait_clks(10);

      // Scenario : Trigger combo Detect to Idle state via
      //            deassertion of input signals
      // Set combo input to trigger precondition
      config_combo_register(i);
      // Wait for 3 clock cycles to sync the register value
      cfg.clk_aon_rst_vif.wait_clks(3);
      reset_combo_inputs(~trigger_combo_precondition[i]);
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer + set_duration_precondition[i] + 10);
      // Set combo input to trigger combo detection
      reset_combo_inputs(~trigger_combo[i], ~trigger_combo_precondition[i]);
      // Wait for some time but dont exceed detect time
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer + set_duration[i] - 10);
      // Deassert combo inputs before detect timer
      reset_combo_inputs();
      cfg.clk_aon_rst_vif.wait_clks(20);

      check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(0));
      // Reset combo registers
      config_combo_register(i, 16'h0);
    end
  endtask

  task combo_action_ec_rst_l_i_assert();
    `uvm_info(`gfn, "ec_rst_l_i assertion check for combo detect", UVM_LOW)
    for (int i = 0; i < 4; i++) begin
      `uvm_info(`gfn, $sformatf("configuring combo channel %0d", i), UVM_LOW)
      // Scenario : Assert ec_rst_l_i just before combo action triggers ec_rst_l_o
      config_combo_register(i);
      reset_combo_inputs(~trigger_combo_precondition[i]);
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer + set_duration_precondition[i] + 10);
      reset_combo_inputs(~trigger_combo[i], ~trigger_combo_precondition[i]);
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer + set_duration[i] - 5);
      fork
        begin
          // Assert ec_rst_l_i signal
          cfg.vif.ec_rst_l_in = 1'b0;
          cfg.clk_aon_rst_vif.wait_clks(10);
          cfg.vif.ec_rst_l_in = 1'b1;
          cfg.clk_aon_rst_vif.wait_clks(set_pulse_width + 10);
        end
        begin
          cfg.clk_aon_rst_vif.wait_clks(5);
          monitor_ec_rst_low(set_pulse_width);
        end
      join
      `uvm_info(`gfn, "ec_rst_l_o asserted as expected", UVM_LOW)
      // Reset combo inputs
      reset_combo_inputs();
      // Disable combo detect
      config_combo_register(i, 0);
    end
  endtask

  task set_edge_detector_input(string field_name, bit reset = 1);
    // Select the edge detect input
    case (field_name)
      "pwrb_in_h2l": cfg.vif.pwrb_in = reset ? 1 : 0;
      "pwrb_in_l2h": cfg.vif.pwrb_in = reset ? 0 : 1;
      "key0_in_h2l": cfg.vif.key0_in = reset ? 1 : 0;
      "key0_in_l2h": cfg.vif.key0_in = reset ? 0 : 1;
      "key1_in_h2l": cfg.vif.key1_in = reset ? 1 : 0;
      "key1_in_l2h": cfg.vif.key1_in = reset ? 0 : 1;
      "key2_in_h2l": cfg.vif.key2_in = reset ? 1 : 0;
      "key2_in_l2h": cfg.vif.key2_in = reset ? 0 : 1;
      "ac_present_l2h": cfg.vif.ac_present = reset ? 0 : 1;
      "ac_present_h2l": cfg.vif.ac_present = reset ? 1 : 0;
      "flash_wp_l_h2l": cfg.vif.flash_wp_l_in = reset ? 1 : 0;
      "flash_wp_l_l2h": cfg.vif.flash_wp_l_in = reset ? 0 : 1;
      "ec_rst_l_h2l": cfg.vif.ec_rst_l_in = reset ? 1 : 0;
      "ec_rst_l_l2h": cfg.vif.ec_rst_l_in = reset ? 0 : 1;
      default: `uvm_error(`gfn,$sformatf("Unknown field name %s", field_name))
    endcase
    cfg.clk_aon_rst_vif.wait_clks(3);
  endtask

  task edge_detect_en(uvm_reg_data_t field_mask);
    uvm_reg_data_t rdata;
    csr_rd(ral.key_intr_ctl, rdata);
    csr_wr(ral.key_intr_ctl, rdata | field_mask);
    cfg.clk_aon_rst_vif.wait_clks(3);
  endtask

  task edge_detect_dis(uvm_reg_data_t field_mask);
    uvm_reg_data_t rdata;
    csr_rd(ral.key_intr_ctl, rdata);
    csr_wr(ral.key_intr_ctl, rdata & ~field_mask);
    cfg.clk_aon_rst_vif.wait_clks(3);
  endtask

  // Key intrrrupt control Debounce to idle state transition
  // 1. disable config before debounce
  // 2. disable config after debounce and before detect time
  task key_intr_debounce_to_idle();
    dv_base_reg_field fields[] = {
      ral.key_intr_ctl.pwrb_in_h2l,
      ral.key_intr_ctl.pwrb_in_l2h,
      ral.key_intr_ctl.key0_in_h2l,
      ral.key_intr_ctl.key0_in_l2h,
      ral.key_intr_ctl.key1_in_h2l,
      ral.key_intr_ctl.key1_in_l2h,
      ral.key_intr_ctl.key2_in_h2l,
      ral.key_intr_ctl.key2_in_l2h,
      ral.key_intr_ctl.ac_present_h2l,
      ral.key_intr_ctl.ac_present_l2h,
      ral.key_intr_ctl.ec_rst_l_h2l,
      ral.key_intr_ctl.ec_rst_l_l2h,
      ral.key_intr_ctl.flash_wp_l_h2l,
      ral.key_intr_ctl.flash_wp_l_l2h
    };

    // Set the key interrupt debounce timer value
    csr_wr(ral.key_intr_debounce_ctl, set_key_intr_timer);

    for (int i = 0; i < fields.size(); i += 1) begin
      string field_name = fields[i].get_name();
      uvm_reg_data_t field_mask = fields[i].get_field_mask();
      `uvm_info(`gfn, $sformatf("checking debounce to idle transition for %s", field_name), UVM_LOW)
      // Scenario : Disable edge detect before debounce timer
      // Reset input
      set_edge_detector_input(field_name);
      // Enable edge detection
      edge_detect_en(field_mask);
      set_edge_detector_input(field_name, 0);
      // Disable edge detection before debounce timer
      cfg.clk_aon_rst_vif.wait_clks(set_key_timer - 6);
      edge_detect_dis(field_mask);
      // Wait till debounce time expires
      cfg.clk_aon_rst_vif.wait_clks(10);
      // Reset input
      set_edge_detector_input(field_name);
      // Wait for pulse width in case of ec_rst_l_h2l
      if (field_name == "ec_rst_l_h2l") cfg.clk_aon_rst_vif.wait_clks(set_pulse_width + 10);
    end
  endtask

  task auto_block_debounce_to_idle();
    // Deassert key inputs
    cfg.vif.key0_in = 1;
    cfg.vif.key1_in = 1;
    cfg.vif.key2_in = 1;
    cfg.vif.pwrb_in = 1;
    cfg.clk_aon_rst_vif.wait_clks(3);
    // Set the auto block key
    csr_wr(ral.auto_block_out_ctl, auto_block_out_ctl);
    cfg.clk_aon_rst_vif.wait_clks(3);
    // Enable the auto block key feature
    ral.auto_block_debounce_ctl.auto_block_enable.set(1'b1);
    ral.auto_block_debounce_ctl.debounce_timer.set(auto_block_debounce_ctl);
    csr_update(ral.auto_block_debounce_ctl);
    cfg.clk_aon_rst_vif.wait_clks(3);
    // Assert key inputs
    cfg.vif.key0_in = 0;
    cfg.vif.key1_in = 0;
    cfg.vif.key2_in = 0;
    cfg.clk_aon_rst_vif.wait_clks(3);
    fork
      begin
        // Scenario : assert pwrb_in and disable auto block before debounce time
        // Assert pwrb_in
        cfg.vif.pwrb_in = 0;
        cfg.clk_aon_rst_vif.wait_clks(set_key_timer - 10);
        // Disable auto block before debounce timer
        ral.auto_block_debounce_ctl.auto_block_enable.set(1'b0);
        csr_update(ral.auto_block_debounce_ctl);
        cfg.clk_aon_rst_vif.wait_clks(10);
        cfg.vif.pwrb_in = 1;
      end
      // Check for key outputs
      begin
        repeat (20) `DV_CHECK_EQ(cfg.vif.key0_in, cfg.vif.key0_out)
      end
      begin
        repeat (20) `DV_CHECK_EQ(cfg.vif.key1_in, cfg.vif.key1_out)
      end
      begin
        repeat (20) `DV_CHECK_EQ(cfg.vif.key2_in, cfg.vif.key2_out)
      end
    join
    // Release key inputs
    cfg.vif.key0_in = 0;
    cfg.vif.key1_in = 0;
    cfg.vif.key2_in = 0;
  endtask

  task drive_ac(uint16_t cycles);
    cfg.vif.ac_present = 1;
    cfg.clk_aon_rst_vif.wait_clks(cycles);
    cfg.vif.ac_present = 0;
  endtask

  task drive_pwrb(uint16_t cycles);
    cfg.vif.pwrb_in = 1;
    cfg.clk_aon_rst_vif.wait_clks(1);
    cfg.vif.pwrb_in = 0;
    cfg.clk_aon_rst_vif.wait_clks(cycles);
    cfg.vif.pwrb_in = 1;
  endtask

  task drive_lid(uint16_t cycles);
    cfg.vif.lid_open = 0;
    cfg.clk_aon_rst_vif.wait_clks(1);
    cfg.vif.lid_open = 1;
    cfg.clk_aon_rst_vif.wait_clks(cycles);
    cfg.vif.lid_open = 0;
  endtask

  task ulp_debounce_to_idle();
    `uvm_info(`gfn, "Executing task to trigger deebounce to idle state transition in ULP", UVM_LOW)
    // Scenario: disable ULP feature before debounce timer
    // Program ULP registers
    // Set the debounce timer for pwrb_in, ac_present and lid_open
    csr_wr(ral.ulp_ac_debounce_ctl, ulp_debounce_ctl);
    csr_wr(ral.ulp_lid_debounce_ctl, ulp_debounce_ctl);
    csr_wr(ral.ulp_pwrb_debounce_ctl, ulp_debounce_ctl);
    // Enable ultra low power feature
    ral.ulp_ctl.ulp_enable.set(1'b1);
    csr_update(ral.ulp_ctl);
    // Wait for registers to update
    cfg.clk_aon_rst_vif.wait_clks(2);
    // Drive ULP key inputs for debounce time and disable ULP before debounce time
    fork
      begin
        drive_ac(ulp_debounce_ctl + 10);
      end
      begin
        drive_pwrb(ulp_debounce_ctl + 10);
      end
      begin
        drive_lid(ulp_debounce_ctl + 10);
      end
      begin
        cfg.clk_aon_rst_vif.wait_clks(ulp_debounce_ctl - 10);
        // Disable ultra low power feature
        ral.ulp_ctl.ulp_enable.set(1'b0);
        csr_update(ral.ulp_ctl);
        cfg.clk_aon_rst_vif.wait_clks(2);
      end
    join
    // Check ULP status
    csr_rd_check(ral.ulp_status, .compare_value(0));
    // Scenario: deassert input signal before debounce timer
    // Enable ultra low power feature
    ral.ulp_ctl.ulp_enable.set(1'b1);
    csr_update(ral.ulp_ctl);
    // It takes 2-3 clock cycles to sync the register values
    cfg.clk_aon_rst_vif.wait_clks(2);
    // Disable the bus clock
    cfg.clk_rst_vif.stop_clk();
    cfg.clk_aon_rst_vif.wait_clks(2);
    // Drive ULP key inputs for debounce time and deassert before debounce time
    fork
      begin
        drive_ac(ulp_debounce_ctl - 10);
      end
      begin
        drive_pwrb(ulp_debounce_ctl - 10);
      end
      begin
        drive_lid(ulp_debounce_ctl - 10);
      end
    join
    // Enable the bus clock to read the status register
    cfg.clk_rst_vif.start_clk();
    // Check ULP status
    csr_rd_check(ral.ulp_status, .compare_value(0));
    // Disable ultra low power feature
    ral.ulp_ctl.ulp_enable.set(1'b0);
    csr_update(ral.ulp_ctl);
    cfg.clk_aon_rst_vif.wait_clks(2);
  endtask

  task body();
    `uvm_info(`gfn, "Starting the body from feature disable", UVM_LOW)
    combo_debounce_to_idle();
    combo_action_ec_rst_l_i_assert();
    key_intr_debounce_to_idle();
    auto_block_debounce_to_idle();
    ulp_debounce_to_idle();
  endtask
endclass : sysrst_ctrl_feature_disable_vseq
