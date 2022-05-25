// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Test hardware and software reset
class adc_ctrl_fsm_reset_vseq extends adc_ctrl_base_vseq;

  // Configuration
  rand int pwrup_time;
  rand int wakeup_time;
  rand int np_sample_cnt;
  rand int lp_sample_cnt;
  rand adc_ctrl_testmode_e testmode;

  // backdoor load values
  rand int wakeup_time_load_val;
  rand int np_sample_cnt_load_val;
  rand int lp_sample_cnt_load_val;


  // Delay before applying reset (aon clocks)
  rand int reset_delay;
  // Reset to apply
  rand adc_ctrl_reset_mode_e reset_mode;
  // Number of transfers to wait for
  rand int num_txfers;
  // adc_ctrl has been enabled
  event adc_ctrl_enable_ev;

  `uvm_object_utils_begin(adc_ctrl_fsm_reset_vseq)
    `uvm_field_enum(adc_ctrl_testmode_e, testmode, UVM_DEFAULT)
    `uvm_field_enum(adc_ctrl_reset_mode_e, reset_mode, UVM_DEFAULT)
    `uvm_field_int(pwrup_time, UVM_DEFAULT)
    `uvm_field_int(wakeup_time, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  // Counter values
  constraint counters_c {
    pwrup_time inside {[0 : 2 ** ADC_CTRL_PWRUP_TIME_WIDTH - 1]};
    wakeup_time inside {[0 : 2 ** ADC_CTRL_WAKEUP_TIME_WIDTH - 1]};
    np_sample_cnt inside {[1 : 2 ** ADC_CTRL_SAMPLE_CTL_WIDTH - 1]};
    lp_sample_cnt inside {[1 : 2 ** ADC_CTRL_LP_SAMPLE_CTL_WIDTH - 1]};

    // Set up backdoor load values
    if (wakeup_time > 20) {
      wakeup_time_load_val inside {[wakeup_time - 3 : wakeup_time - 1]};
    } else {
      wakeup_time_load_val == 0;
    }

    if (np_sample_cnt > 20) {
      np_sample_cnt_load_val inside {[np_sample_cnt - 3 : np_sample_cnt - 1]};
    } else {
      np_sample_cnt_load_val == 0;
    }

    if (lp_sample_cnt > 3) {
      lp_sample_cnt_load_val inside {[lp_sample_cnt - 3 : wakeup_time - 1]};
    } else {
      lp_sample_cnt_load_val == 0;
    }

  }

  constraint reset_delay_c {reset_delay inside {[1 : 400]};}
  constraint num_trans_c {num_trans inside {[100 : 200]};}
  constraint num_txfers_c {num_txfers inside {[1 : 3]};}

  virtual task pre_start();
    super.pre_start();
    // Disable read of intr_state at the end of the sequence
    do_clear_all_interrupts = 0;
    // Disable push/pull assertions
    `DV_ASSERT_CTRL_REQ("ADC_IF_A_CTRL", 0)
    // Disable power up time assertion
    `DV_ASSERT_CTRL_REQ("PwrupTime_A_CTRL", 0)
    // Disable enter low power assertion
    `DV_ASSERT_CTRL_REQ("EnterLowPower_A_CTRL", 0)
    // Disable FSM assertions - need this due to counter preloads
    `DV_ASSERT_CTRL_REQ("ADC_CTRL_FSM_A_CTRL", 0)
  endtask

  virtual task post_start();
    super.post_start();
    // Reenable assertions
    `DV_ASSERT_CTRL_REQ("ADC_IF_A_CTRL", 1)
    `DV_ASSERT_CTRL_REQ("PwrupTime_A_CTRL", 1)
    `DV_ASSERT_CTRL_REQ("EnterLowPower_A_CTRL", 1)
    `DV_ASSERT_CTRL_REQ("ADC_CTRL_FSM_A_CTRL", 1)
  endtask


  virtual task body();
    uvm_reg_data_t rdata;
    // Make sure ADC is off
    csr_wr(ral.adc_en_ctl, 'h0);

    // Make sure filters will always match
    ral.adc_chn0_filter_ctl[0].min_v.set(0);
    ral.adc_chn0_filter_ctl[0].max_v.set(1023);
    ral.adc_chn0_filter_ctl[0].cond.set(ADC_CTRL_FILTER_COND_IN);
    ral.adc_chn0_filter_ctl[0].en.set(1);
    ral.adc_chn1_filter_ctl[0].min_v.set(0);
    ral.adc_chn1_filter_ctl[0].max_v.set(1023);
    ral.adc_chn1_filter_ctl[0].cond.set(ADC_CTRL_FILTER_COND_IN);
    ral.adc_chn1_filter_ctl[0].en.set(1);
    csr_wr(ral.adc_chn0_filter_ctl[0], ral.adc_chn0_filter_ctl[0].get());
    csr_wr(ral.adc_chn1_filter_ctl[0], ral.adc_chn1_filter_ctl[0].get());

    repeat (num_trans) begin
      // Set up sample counts
      csr_wr(ral.adc_sample_ctl, np_sample_cnt);
      csr_wr(ral.adc_lp_sample_ctl, lp_sample_cnt);

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
        default: `uvm_fatal(`gfn, "Undefined test mode")
      endcase

      fork
        begin : guard_proc
          fork
            begin : processing_proc
              // Write registers to enable ADC_CTRL
              csr_wr(ral.adc_pd_ctl, ral.adc_pd_ctl.get());
              csr_wr(ral.adc_en_ctl, ral.adc_en_ctl.get());

              // Sync to aon clock
              cfg.clk_aon_rst_vif.wait_clks(1);
              // Preload the counters to reduce simulation time
              if (wakeup_time_load_val) load_wakeup_timer_cnt_backdoor(wakeup_time_load_val);
              if (np_sample_cnt_load_val) load_np_sample_cnt_backdoor(np_sample_cnt_load_val);
              if (lp_sample_cnt_load_val) load_lp_sample_cnt_backdoor(lp_sample_cnt_load_val);
              ->adc_ctrl_enable_ev;
              // Wait for data transfers
              wait_for_txfers();
            end : processing_proc
            begin : reset_proc
              @(adc_ctrl_enable_ev);
              cfg.clk_aon_rst_vif.wait_clks(reset_delay);
              case (reset_mode)
                AdcCtrlResetModeFsm: begin
                  // Software reset
                  csr_wr(ral.adc_fsm_rst, 1);
                  cfg.clk_aon_rst_vif.wait_clks($urandom_range(5, 10));
                  csr_wr(ral.adc_fsm_rst, 0);
                end
                AdcCtrlResetModeHw: begin
                  // Hardware reset
                  fork
                    cfg.clk_aon_rst_vif.apply_reset();
                    cfg.clk_rst_vif.apply_reset();
                  join
                end
                default: `uvm_fatal(`gfn, "Undefined test mode")
              endcase
            end : reset_proc
          join_any
          wait_no_outstanding_access();
          disable fork;
        end : guard_proc
      join

      // Make sure HW and FSM reset are deasserted
      cfg.clk_aon_rst_vif.drive_rst_pin(1);
      csr_wr(ral.adc_fsm_rst, 0);
      // Disable ADC.
      csr_wr(ral.adc_en_ctl, 0);

      // Re-randomize this sequence
      `DV_CHECK_RANDOMIZE_FATAL(this)
    end
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(5, 10));

  endtask : body

  virtual task wait_for_txfers();
    repeat (num_txfers) wait_all_rx();
  endtask

endclass : adc_ctrl_fsm_reset_vseq
