// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

// Wrapper class to allow for multiple instances
class adc_ctrl_filter_cg_wrapper #(
  // Data width of the ADC CTRL filters
  int FILTER_WIDTH  = ADC_CTRL_DATA_WIDTH,
  // Number of values bins to create
  int NUMBER_VALUES = 10
);

  // Filter configuration one instance per filter
  covergroup adc_ctrl_filter_cg(
      int channel, int filter
  ) with function sample (
      adc_ctrl_filter_cfg_t cfg, bit is_interrupt = 0, bit is_wakeup = 0, bit clk_gate = 0
  );
    option.name = $sformatf("adc_ctrl_filter_cg_%0d_%0d", channel, filter);
    option.per_instance = 1;

    cond_cp: coverpoint cfg.cond;
    min_v_cp: coverpoint cfg.min_v {
      bins minimum = {0};
      bins values[NUMBER_VALUES] = {[1 : (2 ** FILTER_WIDTH - 2)]};
      bins maximum = {2 ** FILTER_WIDTH - 1};
    }
    max_v_cp: coverpoint cfg.max_v {
      bins minimum = {0};
      bins values[NUMBER_VALUES] = {[1 : (2 ** FILTER_WIDTH - 2)]};
      bins maximum = {2 ** FILTER_WIDTH - 1};
    }
    en_cp: coverpoint cfg.en;
    interrupt_cp: coverpoint is_interrupt;
    wakeup_cp: coverpoint is_wakeup;
    clk_gate_cp: coverpoint clk_gate;
    intr_min_v_cond_xp: cross interrupt_cp, min_v_cp, cond_cp;
    intr_max_v_cond_xp: cross interrupt_cp, max_v_cp, cond_cp;
    wakeup_min_v_cond_xp: cross wakeup_cp, min_v_cp, cond_cp;
    wakeup_max_v_cond_xp: cross wakeup_cp, max_v_cp, cond_cp;
    wakeup_gated_xp : cross wakeup_cp, clk_gate_cp;
  endgroup

  function new(int channel, int filter);
    adc_ctrl_filter_cg = new(channel, filter);
  endfunction
endclass

class adc_ctrl_env_cov extends cip_base_env_cov #(
  .CFG_T(adc_ctrl_env_cfg)
);
  `uvm_component_utils(adc_ctrl_env_cov)

  // Sample configuration
  event sample_cfg_ev;

  // covergroups

  // Modes of operation - sampled when adc_en_ctl is written to start the ADC_CTRL
  covergroup adc_ctrl_testmode_cg with function sample (adc_ctrl_testmode_e testmode);
    testmode_cp: coverpoint testmode {
      bins testmodes[] = {AdcCtrlTestmodeOneShot, AdcCtrlTestmodeNormal, AdcCtrlTestmodeLowpower};

      bins transitions[] = ( AdcCtrlTestmodeOneShot, AdcCtrlTestmodeNormal,
      AdcCtrlTestmodeLowpower => AdcCtrlTestmodeOneShot, AdcCtrlTestmodeNormal,
      AdcCtrlTestmodeLowpower );
    }
  endgroup


  // These are sampled on configuration when adc_en_ctl is written to start the ADC_CTRL
  // They are also sampled when an interrupt or wakeup event occurs
  // There is one per filter
  adc_ctrl_filter_cg_wrapper adc_ctrl_filter_cg_wrapper_insts
      [ADC_CTRL_CHANNELS] [ADC_CTRL_NUM_FILTERS];


  function new(string name = "adc_ctrl_env_cov", uvm_component parent = null);
    super.new(name, parent);
    adc_ctrl_testmode_cg = new();
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    for (int channel = 0; channel < ADC_CTRL_CHANNELS; channel++) begin
      for (int filter = 0; filter < ADC_CTRL_NUM_FILTERS; filter++) begin
        adc_ctrl_filter_cg_wrapper_insts[channel][filter] = new(.channel(channel), .filter(filter));
      end
    end
  endfunction : build_phase

  // Sample filter coverage
  virtual function void sample_filter_cov(int channel, int filter, adc_ctrl_filter_cfg_t cfg,
                                          bit is_interrupt = 0, bit is_wakeup = 0,
                                          bit clk_gate = 0);
    adc_ctrl_filter_cg_wrapper_insts[channel][filter].adc_ctrl_filter_cg.sample(cfg, is_interrupt,
                                                                                is_wakeup);
  endfunction

endclass
