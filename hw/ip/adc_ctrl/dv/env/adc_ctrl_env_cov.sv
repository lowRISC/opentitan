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
  // Sampling event
  event sample_ev;
  adc_ctrl_env_cfg cfg;

  // Filter configuration one instance per filter
  covergroup adc_ctrl_filter_cg(int channel, int filter) @(sample_ev);
    option.name = $sformatf("adc_ctrl_filter_cg_%0d_%0d", channel, filter);
    option.per_instance = 1;
    cond_cp: coverpoint cfg.filter_cfg[channel][filter].cond;
    min_v_cp: coverpoint cfg.filter_cfg[channel][filter].min_v {
      bins minimum = {0};
      bins values[NUMBER_VALUES] = {[1 : (2 ** FILTER_WIDTH - 2)]};
      bins maximum = {2 ** FILTER_WIDTH - 1};
    }
    max_v_cp: coverpoint cfg.filter_cfg[channel][filter].max_v {
      bins minimum = {0};
      bins values[NUMBER_VALUES] = {[1 : (2 ** FILTER_WIDTH - 2)]};
      bins maximum = {2 ** FILTER_WIDTH - 1};
    }
    en_cp: coverpoint cfg.filter_cfg[channel][filter].en;
  endgroup

  function new(int channel, int filter, adc_ctrl_env_cfg cfg, event sample_ev);
    this.sample_ev = sample_ev;
    this.cfg = cfg;
    adc_ctrl_filter_cg = new(channel, filter);
  endfunction
endclass

class adc_ctrl_env_cov extends cip_base_env_cov #(
  .CFG_T(adc_ctrl_env_cfg)
);
  `uvm_component_utils(adc_ctrl_env_cov)
  `uvm_component_new

  // Sample configuration
  event sample_cfg_ev;

  // covergroups

  adc_ctrl_filter_cg_wrapper adc_ctrl_filter_cg_wrapper_insts
      [ADC_CTRL_CHANNELS] [ADC_CTRL_NUM_FILTERS];

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    for (int channel = 0; channel < ADC_CTRL_CHANNELS; channel++) begin
      for (int filter = 0; filter < ADC_CTRL_NUM_FILTERS; filter++) begin
        adc_ctrl_filter_cg_wrapper_insts[channel][filter] =
            new(.channel(channel), .filter(filter), .cfg(cfg), .sample_ev(sample_cfg_ev));
      end
    end
  endfunction : build_phase

  // Sample the coverage
  virtual function void sample_cfg_cov();
    ->sample_cfg_ev;
  endfunction

endclass
