// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_env_cfg extends cip_base_env_cfg #(.RAL_T(spi_host_reg_block));

  // reset kinds for core and dut
  string reset_kinds[] = {"HARD", "TL_IF", "CORE_IF"};
  // seq cfg
  spi_host_seq_cfg    seq_cfg;
  // agent cfgs
  rand spi_agent_cfg  m_spi_agent_cfg;

  `uvm_object_param_utils_begin(spi_host_env_cfg)
    `uvm_field_object(m_spi_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

  // core_clk_rst if
  virtual clk_rst_if clk_rst_core_vif;

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);

    // create spi_host agent config obj
    m_spi_agent_cfg = spi_agent_cfg::type_id::create("m_spi_agent_cfg");
    // setup agent in Device mode
    m_spi_agent_cfg.if_mode = Device;
    // drained time of phase_ready_to_end
    m_spi_agent_cfg.ok_to_end_delay_ns = 8000;
    // create req_analysis_fifo for re-active slave agent
    m_spi_agent_cfg.has_req_fifo = 1'b1;
    // default spi_mode
    m_spi_agent_cfg.spi_mode = Single;

    // create the seq_cfg
    seq_cfg = spi_host_seq_cfg::type_id::create("seq_cfg");

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

  // clk_core_freq_mhz is set by
  // - a slower frequency in range [bus_clk(1-s) : bus_clk*(1+s] if en_random is set
  //   where s is a scaling factor (less than 1)
  // - bus_clock frequency otherwise
  virtual function int get_clk_core_freq(real clk_scale, uint en_random = 1);
    int clk_core_min, clk_core_max, clk_core_mhz;

    if (en_random) begin
      `DV_CHECK_LT(clk_scale, 1)
      `uvm_info(`gfn, $sformatf("clk_scale %.2f", clk_scale), UVM_LOW)
      clk_core_max = int'((1 + clk_scale) * real'(clk_rst_vif.clk_freq_mhz));
      clk_core_min = int'((1 - clk_scale) * real'(clk_rst_vif.clk_freq_mhz));
      clk_core_mhz = $urandom_range(clk_core_min, clk_core_max);
    end else begin  // bus and core has same clock frequency
      clk_core_mhz = clk_rst_vif.clk_freq_mhz;
    end
    return clk_core_mhz;
  endfunction : get_clk_core_freq
  
endclass : spi_host_env_cfg
