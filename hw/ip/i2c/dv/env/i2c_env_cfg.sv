// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_env_cfg extends cip_base_env_cfg #(.RAL_T(i2c_reg_block));

  // i2c address mode (only support 7-bit address for targets)
  i2c_target_addr_mode_e target_addr_mode = Addr7BitMode;

  // drained time of phase_ready_to_end
  uint ok_to_end_delay_ns = 5000;

  // i2c_agent cfg
  rand i2c_agent_cfg m_i2c_agent_cfg;

  // seq cfg
  i2c_seq_cfg seq_cfg;

  `uvm_object_utils_begin(i2c_env_cfg)
    `uvm_field_object(m_i2c_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);

    // create i2c_agent_cfg
    m_i2c_agent_cfg = i2c_agent_cfg::type_id::create("m_i2c_agent_cfg");

    // create the seq_cfg
    seq_cfg = i2c_seq_cfg::type_id::create("seq_cfg");

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

  // this function is called after reset or end of vseq run
  virtual function void reset_seq_cfg();
    seq_cfg.en_fmt_overflow     = 1'b0;
    seq_cfg.en_rx_overflow      = 1'b0;
    seq_cfg.en_rx_watermark     = 1'b0;
    seq_cfg.en_sda_unstable     = 1'b0;
    seq_cfg.en_scl_interference = 1'b0;
    seq_cfg.en_sda_interference = 1'b0;
  endfunction : reset_seq_cfg

endclass : i2c_env_cfg
