// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_env_cfg extends cip_base_env_cfg #(.RAL_T(pwm_reg_block));

  // pwm_agent_cfg
  rand pwm_agent_cfg m_pwm_agent_cfg;

  // seq_cfg
  pwm_seq_cfg seq_cfg;

  // clk_rst_core_if
  virtual clk_rst_if clk_rst_core_vif;

  `uvm_object_utils_begin(pwm_env_cfg)
    `uvm_field_object(m_pwm_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);

    // create m_pwm_agent_cfg
    m_pwm_agent_cfg = pwm_agent_cfg::type_id::create("m_pwm_agent_cfg");
    m_pwm_agent_cfg.if_mode = Device; // setup agent in Device mode
    m_pwm_agent_cfg.ok_to_end_delay_ns = 8000; // drained time of phase_ready_to_end

    // create seq_cfg
    seq_cfg = pwm_seq_cfg::type_id::create("seq_cfg");
  endfunction

  // clk_core_freq_mhz is assigned by
  // - a slower frequency in range [bus_clock*scale : bus_clock] if en_random is set (scale <= 1)
  // - bus_clock frequency otherwise
  virtual function int get_clk_core_freq(real core_clk_ratio, uint en_random = 1);
    int clk_core_min, clk_core_max, clk_core_mhz;

    if (en_random) begin
      `DV_CHECK_LE(core_clk_ratio, 1)
      clk_core_max = clk_rst_vif.clk_freq_mhz;
      clk_core_min = int'(core_clk_ratio * real'(clk_rst_vif.clk_freq_mhz));
      clk_core_mhz = $urandom_range(clk_core_min, clk_core_max);
    end else begin
      clk_core_mhz = clk_rst_vif.clk_freq_mhz;
    end
    `uvm_info(`gfn, $sformatf("clk_bus %0d Mhz, clk_core %0d Mhz",
        clk_rst_vif.clk_freq_mhz, clk_core_mhz), UVM_DEBUG)
    `DV_CHECK_LE(clk_core_mhz, clk_rst_vif.clk_freq_mhz)

    return clk_core_mhz;
  endfunction : get_clk_core_freq

endclass : pwm_env_cfg
