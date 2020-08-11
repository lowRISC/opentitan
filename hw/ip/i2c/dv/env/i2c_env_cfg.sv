// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_env_cfg extends cip_base_env_cfg#(
    .RAL_T(i2c_reg_block)
);

  i2c_target_addr_mode_e target_addr_mode = Addr7BitMode;
  uint ok_to_end_delay_ns = I2C_IDLE_TIME;

  // bits to control fifos access
  // set en_fmt_overflow to ensure fmt_overflow irq is triggered
  bit en_fmt_overflow = 1'b0;
  // set en_rx_overflow to ensure ensure rx_overflow irq is triggered
  bit en_rx_overflow = 1'b0;
  // set en_rx_watermark to ensure rx_watermark irq is triggered
  bit en_rx_watermark = 1'b0;

  rand i2c_agent_cfg m_i2c_agent_cfg;

  `uvm_object_utils_begin(i2c_env_cfg)
    `uvm_field_object(m_i2c_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize_csr_addr_map_size();
    this.csr_addr_map_size = I2C_ADDR_MAP_SIZE;
  endfunction : initialize_csr_addr_map_size

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
    m_i2c_agent_cfg = i2c_agent_cfg::type_id::create("m_i2c_agent_cfg");
    num_interrupts = ral.intr_state.get_n_used_bits();
  endfunction

endclass : i2c_env_cfg
