// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_env_cfg extends cip_base_env_cfg #(.RAL_T(pwm_reg_block));
  `uvm_object_utils_begin(pwm_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // Configuration for each monitor in turn.
  pwm_monitor_cfg    m_pwm_monitor_cfg[PWM_NUM_CHANNELS];

  // Interface to the core clock on which the DUT logic itself runs. This logic remains active
  // even when the bus interface is in a low power state (TL-UL clock stopped).
  virtual clk_rst_if clk_rst_core_vif;

  // A scaling used to convert from the clock frequency in clk_rst_vif (the bus clock) to the core
  // clock. This is a ratio, but scaled so 1.0 is represented by 1024. The scaling is constrained to
  // be between 25% and 100%.
  rand int unsigned clk_scale;
  constraint clk_scale_c { clk_scale inside {[256:1024]}; }

  // Method from dv_base_env_cfg. Construct RAL models and fill in monitor configs.
  extern virtual function void initialize(bit [31:0] csr_base_addr = '1);

  // Return the scaled core clock frequency in MHz.
  extern virtual function int get_clk_core_freq();
endclass : pwm_env_cfg

function void pwm_env_cfg::initialize(bit [31:0] csr_base_addr = '1);
  list_of_alerts = pwm_env_pkg::LIST_OF_ALERTS;
  super.initialize(csr_base_addr);

  // Set up the configuration for each of the monitors.
  foreach (m_pwm_monitor_cfg[i]) begin
    m_pwm_monitor_cfg[i] = pwm_monitor_cfg::type_id::create($sformatf("m_pwm_monitor%0d_cfg", i));
    m_pwm_monitor_cfg[i].if_mode = Device;
    m_pwm_monitor_cfg[i].is_active = 0;
    // Monitors identify themselves and their sequence items, for diagnostic/debugging purposes.
    m_pwm_monitor_cfg[i].monitor_id = i;
  end

  // Support only a single outstanding TL item in tlul_adapter
  m_tl_agent_cfg.max_outstanding_req = 1;
endfunction

// Return the scaled core clock frequency in MHz.
function int pwm_env_cfg::get_clk_core_freq();
  real scaled = clk_rst_vif.clk_freq_mhz * clk_scale / 1024;
  `DV_CHECK_FATAL(clk_rst_vif.clk_freq_mhz > 0)
  `DV_CHECK_FATAL(scaled > 0)

  return int'(scaled + 0.5);
endfunction
