// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_base_vseq extends cip_base_vseq #(
  .RAL_T              (adc_ctrl_reg_block),
  .CFG_T              (adc_ctrl_env_cfg),
  .COV_T              (adc_ctrl_env_cov),
  .VIRTUAL_SEQUENCER_T(adc_ctrl_virtual_sequencer)
);

  // ADC agent sequences
  // Send a random sample to each ADC channel and wait for responses
  ast_adc_all_random_seq  m_ast_adc_all_random_seq;
  // Send ramps with random steps to each ADC channel
  ast_adc_random_ramp_seq m_ast_adc_random_ramp_seq;


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
    if (kind == "HARD") begin
      cfg.clk_aon_rst_vif.apply_reset();
    end
    super.apply_reset(kind);
  endtask  // apply_reset

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.clk_aon_rst_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(cfg.clk_aon_rst_vif.clk_period_ps);
    cfg.clk_aon_rst_vif.drive_rst_pin(1);
  endtask

  // Configure the filter registers using values in the config object
  virtual task configure_filters();
    uvm_reg r;
    uvm_reg_field min_v_fld, max_v_fld, cond_fld, en_fld;
    string regname;
    for(int channel=0; channel < AdcCtrlChannels; channel++) begin
      for(int filter=0; filter < AdcCtrlFilters; filter++) begin
        regname = $sformatf("adc_chn%0d_filter_ctl_%0d",channel,filter);
        r = ral.get_reg_by_name(regname);
        if(r==null) `uvm_fatal(`gfn, {"configure_filters: Couldn't find register ",regname})
          // Get fields
          min_v_fld = r.get_field_by_name("min_v");
          max_v_fld = r.get_field_by_name("max_v");
          cond_fld  = r.get_field_by_name("cond");
          en_fld    = r.get_field_by_name("en");
          // Check valid
          if(min_v_fld==null) `uvm_fatal(`gfn, "configure_filters: Couldn't find field min_v")
          if(max_v_fld==null) `uvm_fatal(`gfn, "configure_filters: Couldn't find field max_v")
          if(cond_fld==null) `uvm_fatal(`gfn, "configure_filters: Couldn't find field cond")
          if(en_fld==null) `uvm_fatal(`gfn, "configure_filters: Couldn't find field en")
          // Set values from config object
          min_v_fld.set(cfg.filter_cfg[channel][filter].min_v);
          max_v_fld.set(cfg.filter_cfg[channel][filter].max_v);
          cond_fld.set(cfg.filter_cfg[channel][filter].cond);
          en_fld.set(cfg.filter_cfg[channel][filter].en);
          // Write register
          csr_wr(r,r.get());
      end
    end
  endtask

endclass : adc_ctrl_base_vseq
