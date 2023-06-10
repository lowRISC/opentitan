// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_env_cfg extends cip_base_env_cfg #(.RAL_T(spi_host_reg_block));



  // reset kinds for core and dut
  string reset_kinds[] = {"HARD", "TL_IF", "CORE_IF"};
  // seq cfg
  spi_host_seq_cfg    seq_cfg;
  // agent cfgs
  spi_agent_cfg  m_spi_agent_cfg;

  virtual spi_passthrough_if spi_passthrough_vif;

  // number of dummy cycles in a dummy segment
  rand int    num_dummy;
  int         max_dummy_cycles = 16;
  int         min_dummy_cycles = 0;
  // Setting this variable = 1'b1 makes the scoreboard commit the expected transaction
  // to the queue for checking when writing to the TXFIFO instead of the COMMAND csr.
  // This allow checking of the stretching behaviour.
  bit         tx_stall_check = 1'b0;

  // bumber of address bytes
  rand int    num_cmd_bytes;

  constraint dummy_c {
    num_dummy inside { [min_dummy_cycles:max_dummy_cycles]};
  }

  constraint cmd_bytes_c {
    num_cmd_bytes inside { [seq_cfg.host_spi_min_len:seq_cfg.host_spi_max_len] };
    num_cmd_bytes%4 == 0;
  }



  `uvm_object_param_utils_begin(spi_host_env_cfg)
    `uvm_field_object(m_spi_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new


  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = spi_host_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    // create spi_host agent config obj
    m_spi_agent_cfg = spi_agent_cfg::type_id::create("m_spi_agent_cfg");
    // setup agent in Device mode
    m_spi_agent_cfg.if_mode = Device;
    // drained time of phase_ready_to_end
    m_spi_agent_cfg.ok_to_end_delay_ns = 5000;
    // create req_analysis_fifo for re-active slave agent
    m_spi_agent_cfg.has_req_fifo = 1'b1;
    // default spi_mode
    m_spi_agent_cfg.spi_mode = Standard;
    // default byte order
    m_spi_agent_cfg.byte_order = SPI_HOST_BYTEORDER;
    // make spi behave as realistic spi. (set to 1 byte per transaction)
    m_spi_agent_cfg.num_bytes_per_trans_in_mon = 1;
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
