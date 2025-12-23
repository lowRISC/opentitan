// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Polled filters test sequence
class adc_ctrl_filters_polled_vseq extends adc_ctrl_base_vseq;

  `uvm_object_utils(adc_ctrl_filters_polled_vseq)

  constraint num_trans_c {num_trans inside {[1 : 3]};}

  function new (string name="");
    super.new(name);
  endfunction

  virtual task pre_start();
    super.pre_start();
    fork
      check_adc_ctrl_status();
    join_none
    cfg.testmode = AdcCtrlTestmodeNormal;
  endtask

  virtual task post_start();
    super.post_start();
    // Kill background processes
    disable check_adc_ctrl_status;
  endtask

  // Run a randomised vseq to ramp channel from start_value to end_value
  local task ramp_channel(int unsigned channel, adc_value_t start_value, adc_value_t end_value);
    adc_ctrl_channel_ramp_vseq vseq = adc_ctrl_channel_ramp_vseq::type_id::create("vseq");
    vseq.push_pull_cfg = cfg.m_adc_push_pull_cfg[channel];
    vseq.push_pull_ev = cfg.m_adc_push_pull_ev[channel];
    if (!vseq.randomize() with {
           vseq.ramp_start == start_value;
           vseq.ramp_end == end_value;
           vseq.ramp_step_min == 0;
           vseq.ramp_step_max == 5;
         }) begin
      `uvm_fatal(`gfn, "Failed to randomise ramp vseq")
    end
    vseq.start(null);
  endtask

  // Ramp all channels in parallel from start_value to end_value
  local task ramp_channels(adc_value_t start_value, adc_value_t end_value);
    fork begin : isolation_fork
      for (int i = 0; i < ADC_CTRL_CHANNELS; i++) begin
        automatic int i_ = i;
        fork ramp_channel(i_, start_value, end_value); join_none
      end
      wait fork;
    end join
  endtask

  task run_iteration();
    // Make sure ADC is off
    csr_wr(ral.adc_en_ctl, 'h0);

    // Set up the adc_ctrl registers
    configure_adc_ctrl();

    // Clear interrupt status reg
    csr_wr(ral.adc_intr_status, '1);

    // Check interrupt status is cleared
    csr_rd_check(.ptr(ral.adc_intr_status), .compare_value(0),
                 .err_msg(called_from(`__FILE__, `__LINE__)));

    // Start ADC
    ral.adc_en_ctl.adc_enable.set(1);
    case (cfg.testmode)
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
    csr_wr(ral.adc_pd_ctl, ral.adc_pd_ctl.get());
    csr_wr(ral.adc_en_ctl, ral.adc_en_ctl.get());

    // Hook to do things immediately after the adc_ctrl is enabled
    post_adc_ctrl_enable();

    // Send randomized ramp on all channels - rising
    ramp_channels(0, adc_value_t'('1));

    // Send randomized ramp on all channels - falling
    ramp_channels(adc_value_t'('1), 0);

    // Now turn off ADC_CTRL
    adc_ctrl_off();

    // FSM reset to synchronise RTL & model
    do_adc_fsm_reset();
  endtask

  task body();
    for(int unsigned i = 1; i <= num_trans; i++) begin
      // Re-randomize configuration if enabled and this is after the first iteration
      if (i > 1 && !cfg.filters_fixed) `DV_CHECK_RANDOMIZE_FATAL(cfg)

      run_iteration();
    end
    // A short delay to allow all CDC to complete
    cfg.clk_aon_rst_vif.wait_clks(10);
  endtask : body

  // Check the status registers after every ADC sample (all channels)
  virtual task check_adc_ctrl_status();
    uvm_reg_data_t rdata;
    forever begin
      // Wait for all channels
      wait_all_rx();
      // Delay to allow register to be updated via clock domain crossing
      cfg.clk_aon_rst_vif.wait_clks(10);
      csr_rd(ral.filter_status, rdata);
      // Randomly erase status bits by writing to filter_status
      if ($urandom_range(0, 10) > 9) begin
        csr_wr(ral.filter_status, $urandom());
      end
    end
  endtask

  // Hook to do things immediately after the adc_ctrl is enabled
  virtual task post_adc_ctrl_enable();
  endtask
endclass : adc_ctrl_filters_polled_vseq
