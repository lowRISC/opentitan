// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Check power on/wakeup counters using the assertions in the testbench
// Just randomize pwrup_time and wakeup_time register and enable the ADC_CTRL in one normal mode
// low power mode or oneshot mode
class adc_ctrl_counter_vseq extends adc_ctrl_base_vseq;

  rand int pwrup_time;
  rand int wakeup_time;
  rand adc_ctrl_testmode_e testmode;

  `uvm_object_utils_begin(adc_ctrl_counter_vseq)
    `uvm_field_enum(adc_ctrl_testmode_e, testmode, UVM_DEFAULT)
    `uvm_field_int(pwrup_time, UVM_DEFAULT)
    `uvm_field_int(wakeup_time, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  // Counter values
  constraint counters_c {
    pwrup_time inside {[0 : (2 ** ADC_CTRL_PWRUP_TIME_WIDTH) - 1]};
    wakeup_time inside {[0 : (2 ** ADC_CTRL_WAKEUP_TIME_WIDTH) - 1]};
  }

  constraint num_trans_c {num_trans inside {[10 : 20]};}

  virtual task pre_start();
    super.pre_start();
    // Disable read of intr_state at the end of the sequence
    do_clear_all_interrupts = 0;
    // Disable push/pull assertions
    `DV_ASSERT_CTRL_REQ("ADC_IF_A_CTRL", 0)
  endtask

  virtual task post_start();
    super.post_start();
    // Reenable assertions
    `DV_ASSERT_CTRL_REQ("ADC_IF_A_CTRL", 1)
    // Randomize cfg to get reasonable values for pwrup_time and wakeup_time for
    // a subsequent sequence if this sequence is used in a stress test
    `DV_CHECK_RANDOMIZE_FATAL(cfg)
  endtask

  virtual task body();
    // Disable read of intr_state at the end of the sequence
    do_clear_all_interrupts = 0;

    // Make sure ADC is off
    csr_wr(ral.adc_en_ctl, 'h0);

    repeat (num_trans) begin

      // Copy sequence fields to config object
      cfg.testmode = testmode;
      cfg.pwrup_time = pwrup_time;
      cfg.wakeup_time = wakeup_time;

      // Set up common register fields
      ral.adc_en_ctl.adc_enable.set(1);
      ral.adc_pd_ctl.pwrup_time.set(pwrup_time);
      ral.adc_pd_ctl.wakeup_time.set(wakeup_time);

      // Set up variable register fields
      case (testmode)
        AdcCtrlTestmodeOneShot: begin
          ral.adc_en_ctl.oneshot_mode.set(1);
          ral.adc_pd_ctl.lp_mode.set(0);
        end
        AdcCtrlTestmodeNormal: begin
          ral.adc_en_ctl.oneshot_mode.set(0);
          ral.adc_pd_ctl.lp_mode.set(0);
        end
        AdcCtrlTestmodeLowpower: begin
          ral.adc_en_ctl.oneshot_mode.set(0);
          ral.adc_pd_ctl.lp_mode.set(1);
        end
        default: `uvm_fatal(`gfn, "Unknown test mode")
      endcase

      // Write registers to enable ADC_CTRL
      csr_wr(ral.adc_pd_ctl, ral.adc_pd_ctl.get());
      csr_wr(ral.adc_en_ctl, ral.adc_en_ctl.get());

      // Wait for data transfers
      wait_for_txfers();

      // Disable ADC.
      csr_wr(ral.adc_en_ctl, 0);

      // Re-randomize this sequence
      `DV_CHECK_RANDOMIZE_FATAL(this)

    end
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(5, 10));

  endtask : body

  virtual task wait_for_txfers();
    wait_all_rx();
  endtask

endclass : adc_ctrl_counter_vseq
