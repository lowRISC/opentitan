// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_base_vseq extends cip_base_vseq #(
  .RAL_T              (adc_ctrl_reg_block),
  .CFG_T              (adc_ctrl_env_cfg),
  .COV_T              (adc_ctrl_env_cov),
  .VIRTUAL_SEQUENCER_T(adc_ctrl_virtual_sequencer)
);

  `uvm_object_utils(adc_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_adc_ctrl_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_adc_ctrl_init) adc_ctrl_init();
  endtask

  virtual task dut_shutdown();
    // check for pending adc_ctrl operations and wait for them to complete
    // TODO
  endtask

  // setup basic adc_ctrl features
  virtual task adc_ctrl_init();
    `uvm_info(`gfn, "Initializating adc_ctrl, nothing to do at the moment", UVM_MEDIUM)
  endtask  // adc_ctrl_init

  virtual task apply_reset(string kind = "HARD");
    // Define 3 kinds of resets - "HARD". "AON", "CORE".
    // HARD reset: reset both, AON and CORE, such that AON encompasses the CORE,
    // as mandated by the spec. AON and CORE: apply those resets individually.
    case (kind)
      "HARD": begin
        fork
          begin
            // Use the main(fast) clock period to constrain the random delay,
            // so we can ensure all resets will be issued within the smallest clock cycle of the
            // design.
            int dly_ps = $urandom_range(0, cfg.clk_rst_vif.clk_period_ps);
            #(dly_ps * 1ps);
            cfg.clk_aon_rst_vif.apply_reset(.rst_n_scheme(0)); // AON reset.
          end
          begin
            super.apply_reset(kind); // CORE reset,
          end
        join
      end
      "CORE": super.apply_reset("HARD");
      "AON": cfg.clk_aon_rst_vif.apply_reset();
      default: `uvm_fatal(`gfn, $sformatf("does not support apply_reset kind: %0s!", kind))
    endcase
  endtask  // apply_reset

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.clk_aon_rst_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(cfg.clk_aon_rst_vif.clk_period_ps);
    cfg.clk_aon_rst_vif.drive_rst_pin(1);
  endtask

  // Configure the dut
  virtual task configure_adc_ctrl();
    uvm_reg r;
    uvm_reg_field min_v_fld, max_v_fld, cond_fld, en_fld;
    string regname;
    `uvm_info(`gfn, "Configuring adc_ctrl", UVM_MEDIUM)
    for (int channel = 0; channel < ADC_CTRL_CHANNELS; channel++) begin
      for (int filter = 0; filter < ADC_CTRL_NUM_FILTERS; filter++) begin
        regname = $sformatf("adc_chn%0d_filter_ctl_%0d", channel, filter);
        r = ral.get_reg_by_name(regname);
        if (r == null) `uvm_fatal(`gfn, {"configure_filters: Couldn't find register ", regname})
        // Get fields
        min_v_fld = r.get_field_by_name("min_v");
        max_v_fld = r.get_field_by_name("max_v");
        cond_fld  = r.get_field_by_name("cond");
        en_fld    = r.get_field_by_name("en");
        // Check valid
        if (min_v_fld == null) `uvm_fatal(`gfn, "configure_filters: Couldn't find field min_v")
        if (max_v_fld == null) `uvm_fatal(`gfn, "configure_filters: Couldn't find field max_v")
        if (cond_fld == null) `uvm_fatal(`gfn, "configure_filters: Couldn't find field cond")
        if (en_fld == null) `uvm_fatal(`gfn, "configure_filters: Couldn't find field en")
        // Set values from config object
        min_v_fld.set(cfg.filter_cfg[channel][filter].min_v);
        max_v_fld.set(cfg.filter_cfg[channel][filter].max_v);
        cond_fld.set(cfg.filter_cfg[channel][filter].cond);
        en_fld.set(cfg.filter_cfg[channel][filter].en);
        // Write register
        csr_wr(r, r.get());
      end
    end
    // Set up sample counts
    csr_wr(ral.adc_sample_ctl, cfg.np_sample_cnt);
    csr_wr(ral.adc_lp_sample_ctl, cfg.lp_sample_cnt);
    // Power control
    ral.adc_pd_ctl.lp_mode.set(cfg.testmode inside {AdcCtrlTestmodeLowpower});
    ral.adc_pd_ctl.pwrup_time.set(cfg.pwrup_time);
    ral.adc_pd_ctl.wakeup_time.set(cfg.wakeup_time);
    csr_wr(ral.adc_pd_ctl, ral.adc_pd_ctl.get());


  endtask

  //
  // Wait for RX on all ADC channels by monitoring channel rx event
  // these are triggered in the scoreboard as items are received
  virtual task wait_all_rx;
    fork
      begin : guard_proc
        for (int idx = 0; idx < ADC_CTRL_CHANNELS; idx++) begin
          // Local copy see LRM 9.3.2 for details
          int idx_local = idx;
          fork
            cfg.wait_adc_rx_event(idx_local);
          join_none
        end
        wait fork;
      end
    join
  endtask

  // Create a string with "called from (filename:line number)" to be used in csr checks etc.
  virtual function string called_from(string filename, int lineno);
    return $sformatf("called from (%s:%0d)", filename, lineno);
  endfunction

  // Turn off ADC CTRL without triggering assertions
  virtual task adc_ctrl_off();
    // Disable assertions which will trigger because of the abrupt turn off
    `DV_ASSERT_CTRL_REQ("ADC_IF_A_CTRL", 0)
    // Sync to data
    wait_all_rx();
    // Delay to allow handshake to complete
    cfg.clk_aon_rst_vif.wait_clks(5);
    // Disable ADC_CTRL
    csr_wr(ral.adc_en_ctl, 'h0);
    // Need to wait long enough for any current ADC access to complete
    // This will be determined by the push pull agent configuration
    cfg.clk_aon_rst_vif.wait_clks(40);
    // Turn back on again
    `DV_ASSERT_CTRL_REQ("ADC_IF_A_CTRL", 1)
  endtask

  // Perform software reset
  virtual task do_adc_fsm_reset();
    // Disable assertions which will trigger because of the abrupt reset
    `DV_ASSERT_CTRL_REQ("ADC_IF_A_CTRL", 0)
    csr_wr(ral.adc_fsm_rst, 1);
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(5, 10));
    csr_wr(ral.adc_fsm_rst, 0);
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(5, 10));
    // Re-enable assertions
    `DV_ASSERT_CTRL_REQ("ADC_IF_A_CTRL", 1)
  endtask

  // Deposit a value via DPI and issue a fatal error if it failed
  virtual function void load_backdoor(input string path, input uvm_hdl_data_t value);
    int retval;
    retval = uvm_hdl_deposit(path, value);
    `DV_CHECK_FATAL(retval, {"uvm_hdl_deposit failed for path ", path})
  endfunction

  // Load counters backdoor using DPI
  // This is used to reduce the time required for tests
  virtual function void load_pwrup_timer_cnt_backdoor(input uvm_hdl_data_t value);
    load_backdoor("tb.dut.u_adc_ctrl_core.u_adc_ctrl_fsm.pwrup_timer_cnt_q", value);
  endfunction

  virtual function void load_wakeup_timer_cnt_backdoor(input uvm_hdl_data_t value);
    load_backdoor("tb.dut.u_adc_ctrl_core.u_adc_ctrl_fsm.wakeup_timer_cnt_q", value);
  endfunction

  virtual function void load_np_sample_cnt_backdoor(input uvm_hdl_data_t value);
    load_backdoor("tb.dut.u_adc_ctrl_core.u_adc_ctrl_fsm.np_sample_cnt_q", value);
  endfunction

  virtual function void load_lp_sample_cnt_backdoor(input uvm_hdl_data_t value);
    load_backdoor("tb.dut.u_adc_ctrl_core.u_adc_ctrl_fsm.lp_sample_cnt_q", value);
  endfunction

endclass : adc_ctrl_base_vseq
