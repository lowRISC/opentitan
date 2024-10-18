// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_env_cfg extends cip_base_env_cfg #(.RAL_T(pwm_reg_block));
  `uvm_object_utils_begin(pwm_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

    // configs
  pwm_monitor_cfg       m_pwm_monitor_cfg[PWM_NUM_CHANNELS];

  // virtual ifs
  virtual clk_rst_if    clk_rst_core_vif;
  int                   core_clk_freq_mhz;

  // variables
  param_reg_t           pwm_param[PWM_NUM_CHANNELS];
  // ratio between bus_clk and core_clk (must be >= 1)
  rand int clk_ratio;
  constraint clk_ratio_c { clk_ratio inside {[1: 4]}; }

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = pwm_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    // create pwm_agent_cfg
    foreach (m_pwm_monitor_cfg[i]) begin
      m_pwm_monitor_cfg[i] = pwm_monitor_cfg::type_id::create($sformatf("m_pwm_monitor%0d_cfg", i));
      m_pwm_monitor_cfg[i].if_mode = Device;
      m_pwm_monitor_cfg[i].is_active = 0;
      m_pwm_monitor_cfg[i].monitor_id = i;
    end

    // only support 1 outstanding TL items in tlul_adapter
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction

  // clk_core_freq_mhz is assigned by
  // - a slower frequency in range [bus_clock*scale : bus_clock] if en_random is set (scale <= 1)
  // - bus_clock frequency otherwise
  virtual function int get_clk_core_freq(uint en_random = 1);
    int clk_core_min, clk_core_max, clk_core_mhz;

    if (en_random) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(clk_ratio)
      `DV_CHECK_GE(clk_ratio, 1)
      clk_core_max = clk_rst_vif.clk_freq_mhz;
      clk_core_min = int'(clk_rst_vif.clk_freq_mhz / clk_ratio);
      clk_core_mhz = $urandom_range(clk_core_min, clk_core_max);
    end else begin
      clk_core_mhz = clk_rst_vif.clk_freq_mhz;
    end
    return clk_core_mhz;
  endfunction : get_clk_core_freq
endclass : pwm_env_cfg
