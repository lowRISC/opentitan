// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Smoke Test Vseq
// Verify datapath between AST ADC interface and ADC sample registers.
//
// Stimulus:
//
// For a number of iterations:
// - Configure DUT no filters or events.
// - Generate ADC data.
// - Sample into capture registers using oneshot mode.
//
// Checks:
//
// - From monitored ADC data predict the value of the ADC sample register
// - Compare sample registers against expected.
// - Check oneshot bit of interrupt status register works as expected.
//
class adc_ctrl_smoke_vseq extends adc_ctrl_base_vseq;

  `uvm_object_utils(adc_ctrl_smoke_vseq)

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    cfg.testmode = AdcCtrlTestmodeOneShot;
    cfg.adc_intr_ctl = 0;
    cfg.adc_wakeup_ctl = 0;
  endtask

  task body();
    uvm_reg_data_t rdata;
    // Vector with onehot interrupt status bit position = 1
    const uvm_reg_data_t ONE_SHOT_INTR = 1 << ral.adc_intr_status.oneshot.get_lsb_pos();

    // Make sure ADC is off
    csr_wr(ral.adc_en_ctl, 'h0);

    // Set one shot interrupt enable
    csr_wr(ral.adc_intr_ctl, ONE_SHOT_INTR);
    // Copy to config object for scoreboard
    cfg.adc_intr_ctl = ONE_SHOT_INTR;

    // Configure power control register
    ral.adc_pd_ctl.pwrup_time.set(cfg.pwrup_time);
    ral.adc_pd_ctl.wakeup_time.set(cfg.wakeup_time);
    csr_wr(ral.adc_pd_ctl, ral.adc_pd_ctl.get());

    repeat (20) begin

      // Clear interrupt status reg
      csr_wr(ral.adc_intr_status, '1);

      // Check interrupt status
      csr_rd_check(.ptr(ral.adc_intr_status), .compare_value(0),
                   .err_msg(called_from(`__FILE__, `__LINE__)));

      // Trigger oneshot sample
      ral.adc_en_ctl.adc_enable.set(1);
      ral.adc_en_ctl.oneshot_mode.set(1);
      csr_wr(ral.adc_en_ctl, ral.adc_en_ctl.get());

      wait_all_rx();
      // Give time to settle
      #20us;

      // Check interrupt status
      csr_rd_check(.ptr(ral.adc_intr_status), .compare_value(ONE_SHOT_INTR),
                   .err_msg(called_from(`__FILE__, `__LINE__)));

      // Read and check ADC value registers - check performed in scoreboard
      csr_rd(ral.adc_chn_val[0], rdata);
      csr_rd(ral.adc_chn_val[1], rdata);

      // Turn off ADC
      csr_wr(ral.adc_en_ctl, 'h0);

    end

    // Allow time for sim to finish or we trigger an assertion
    #100us;
  endtask : body

endclass : adc_ctrl_smoke_vseq
