// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Filters wakeup test sequence
class adc_ctrl_filters_wakeup_vseq extends adc_ctrl_filters_polled_vseq;

  `uvm_object_utils(adc_ctrl_filters_wakeup_vseq)

  `uvm_object_new

  virtual task post_start();
    // Kill background processes
    disable check_adc_ctrl_status;
    super.post_start();
  endtask

  virtual task configure_adc_ctrl();
    bit [ADC_CTRL_NUM_FILTERS-1:0] adc_wakeup_ctl;
    super.configure_adc_ctrl();
    `DV_CHECK_STD_RANDOMIZE_FATAL(adc_wakeup_ctl)
    // Low power mode
    cfg.testmode = AdcCtrlTestmodeLowpower;
    // Enable wakeup
    cfg.adc_wakeup_ctl = adc_wakeup_ctl;
    csr_wr(ral.adc_wakeup_ctl, cfg.adc_wakeup_ctl);
  endtask

  // Check the ADC CTRL status after every ADC sample (all channels)
  virtual task check_adc_ctrl_status();
    uvm_reg_data_t rdata;
    forever begin
      // Wait for all channels
      wait_all_rx();
      // Delay to allow register to be updated
      cfg.clk_aon_rst_vif.wait_clks(10);
      //csr_rd(ral.adc_wakeup_status, rdata);
      csr_rd(ral.filter_status, rdata);
      // Randomly erase adc_wakeup_status
      if ($urandom_range(0, 10) > 9) begin
        csr_wr(ral.filter_status, $urandom());
      end
    end
  endtask

endclass : adc_ctrl_filters_wakeup_vseq
