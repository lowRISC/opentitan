// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_base_test extends cip_base_test#(
    .ENV_T(chip_env), .CFG_T(chip_env_cfg)
);
  `uvm_component_utils(chip_base_test)
  `uvm_component_new

  // The base class dv_base_test creates the following instances:
  // chip_env_cfg: cfg
  // chip_env:     env

  // The base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done.

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Knob to en/dis stubbing cpu (disabled by default).
    void'($value$plusargs("stub_cpu=%0b", cfg.stub_cpu));
    // Set tl_agent's is_active bit based on the retrieved stub_cpu value.
    cfg.m_tl_agent_cfg.is_active = cfg.stub_cpu;

    // Knob to set the UART baud rate (set to 2M by default).
    void'($value$plusargs("uart_baud_rate=%0d", cfg.uart_baud_rate));

    // Knob to configure writing sw logs to a separate file (enabled by default).
    void'($value$plusargs("write_sw_logs_to_file=%0b", cfg.write_sw_logs_to_file));

    // Knob to enable logging over UART (disabled by default).
    void'($value$plusargs("en_uart_logger=%0b", cfg.en_uart_logger));
    cfg.m_uart_agent_cfg.en_logger = cfg.en_uart_logger;
    cfg.m_uart_agent_cfg.write_logs_to_file = cfg.write_sw_logs_to_file;

    // Knob to set the sw_test_timeout_ns (set to 5ms by default).
    void'($value$plusargs("sw_test_timeout_ns=%0d", cfg.sw_test_timeout_ns));

    // Knob to pre-initialize RAM to 0s (disabled by default).
    void'($value$plusargs("initialize_ram=%0b", cfg.initialize_ram));

    // override tl_seq_item to apply constraint on source_id
    tl_seq_item::type_id::set_type_override(chip_tl_seq_item::get_type());
  endfunction : build_phase

endclass : chip_base_test
