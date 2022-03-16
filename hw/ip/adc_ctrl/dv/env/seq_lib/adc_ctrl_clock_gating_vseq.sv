// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Test ADC_CTRL can wakeup the system even when the fast clock is switched off
// Enable DUT with interrupts and wakeup then switch off the fast clock
// When a positive edge on the wakeup signal is detected switch the fast clock back on
// As register access requires the fast clock, it's disabled that while the fast clock is off
class adc_ctrl_clock_gating_vseq extends adc_ctrl_filters_polled_vseq;

  bit m_fast_clock_gated = 0;

  `uvm_object_utils(adc_ctrl_clock_gating_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    fork
      monitor_wakeup();
    join_none
  endtask

  virtual task post_start();
    // Make sure clock is ungated and kill monitor_wakeup process
    disable monitor_wakeup;
    cfg.clk_rst_vif.start_clk(0);
    super.post_start();
  endtask

  virtual task configure_adc_ctrl();
    adc_ctrl_testmode_e testmode;
    bit [ADC_CTRL_NUM_FILTERS:0] adc_intr_ctl;
    bit [ADC_CTRL_NUM_FILTERS-1:0] adc_wakeup_ctl;

    super.configure_adc_ctrl();
    // Normal or low power
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
        testmode, testmode inside {AdcCtrlTestmodeNormal, AdcCtrlTestmodeLowpower};)
    // Enable interrupts and wakeup
    `DV_CHECK_STD_RANDOMIZE_FATAL(adc_intr_ctl)
    `DV_CHECK_STD_RANDOMIZE_FATAL(adc_wakeup_ctl)
    cfg.testmode = testmode;
    cfg.adc_intr_ctl = adc_intr_ctl;
    cfg.adc_wakeup_ctl = adc_wakeup_ctl;
    csr_wr(ral.adc_wakeup_ctl, cfg.adc_wakeup_ctl);
    csr_wr(ral.adc_intr_ctl, cfg.adc_intr_ctl);
    csr_wr(ral.intr_enable, 'h1);
  endtask

  // Hook to do things immediately after the adc_ctrl is enabled
  virtual task post_adc_ctrl_enable();
    wait_no_outstanding_access();
    // Turn off fast clock
    cfg.clk_rst_vif.stop_clk();
    m_fast_clock_gated = 1;
  endtask

  // Check the ADC CTRL status after every ADC sample (all channels)
  virtual task check_adc_ctrl_status();
    uvm_reg_data_t rdata;
    forever begin
      // Wait for all channels
      wait_all_rx();

      // Register access only when fast clock is active
      if (!m_fast_clock_gated) begin
        // Delay to allow register to be updated
        cfg.clk_aon_rst_vif.wait_clks(10);
        csr_rd(ral.intr_state, rdata);
        csr_rd(ral.adc_intr_status, rdata);
        csr_rd(ral.filter_status, rdata);
        // Randomly erase intr_status/state
        if ($urandom_range(0, 10) > 9) begin
          csr_wr(ral.adc_intr_status, $urandom());
          csr_wr(ral.filter_status, $urandom());
          csr_wr(ral.intr_state, $urandom());
        end
      end
    end
  endtask

  // Turn off ADC CTRL without triggering assertions
  virtual task adc_ctrl_off();
    // Make sure clock is turned back on
    `uvm_info(`gfn, "adc_ctrl_off:", UVM_LOW)
    cfg.clk_rst_vif.start_clk(1);
    m_fast_clock_gated = 0;
    super.adc_ctrl_off();
  endtask

  // Monitor wakeup signal and re-enable clock on postitive edge
  virtual task monitor_wakeup();
    bit wakeup = 0, wakeup_prev = 0;
    forever begin
      cfg.clk_aon_rst_vif.wait_clks(1);
      wakeup_prev = wakeup;
      wakeup = cfg.wakeup_vif.sample_pin(0);
      if (wakeup & ~wakeup_prev) begin
        // Delay a random number of clocks
        cfg.clk_aon_rst_vif.wait_clks($urandom_range(0, 100));
        // Turn on fast clock
        cfg.clk_rst_vif.start_clk(1);
        m_fast_clock_gated = 0;
      end
    end
  endtask

endclass : adc_ctrl_clock_gating_vseq
