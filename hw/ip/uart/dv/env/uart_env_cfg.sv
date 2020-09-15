// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_env_cfg extends cip_base_env_cfg #(.RAL_T(uart_reg_block));

  // ext component cfgs
  rand uart_agent_cfg   m_uart_agent_cfg;
  // during break error, DUT will trigger additional frame/parity errors, which mon doesn't catch
  // disable parity/frame check in this period
  bit  disable_scb_rx_parity_check;
  bit  disable_scb_rx_frame_check;

  `uvm_object_utils_begin(uart_env_cfg)
    `uvm_field_object(m_uart_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
    // create uart agent config obj
    m_uart_agent_cfg = uart_agent_cfg::type_id::create("m_uart_agent_cfg");
    // set num_interrupts & num_alerts which will be used to create coverage and more
    num_interrupts = ral.intr_state.get_n_used_bits();
    // only support 1 outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction

  // uart doesn't have reset pin. When reset occurs/clears,
  // need to call reset function in uart_agent_cfg
  virtual function void reset_asserted();
    super.reset_asserted();
    m_uart_agent_cfg.reset_asserted();
  endfunction

  virtual function void reset_deasserted();
    super.reset_deasserted();
    m_uart_agent_cfg.reset_deasserted();
  endfunction
endclass
