// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_agent_cfg extends dv_base_agent_cfg;

  // agent cfg knobs
  bit is_active         = 1'b1; // active driver or passive monitor
  bit en_cov            = 1'b1; // enable coverage
  bit en_rx_checks      = 1'b1; // enable RX checks (implemented in monitor)
  bit en_tx_checks      = 1'b1; // enable TX checks (implemented in monitor)
  bit en_rx_monitor     = 1'b1; // enable RX monitor
  bit en_tx_monitor     = 1'b1; // enable TX monitor
  bit en_loopback       = 1'b0; // enable TX -> RX loopback;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual i2c_if  vif;

  // random variable and their constrains
  int max_dly_to_send_nack    = 5;
  int max_dly_to_send_ack     = 5;
  int max_dly_to_send_stop    = 5;
  int max_dly_to_send_rd_data = 5;

  rand int dly_to_send_nack;
  rand int dly_to_send_ack;
  rand int dly_to_send_stop;
  rand int dly_to_send_rd_data;

  constraint dly_to_send_ack_c     { dly_to_send_ack     inside {[1:max_dly_to_send_ack]}; }
  constraint dly_to_send_nack_c    { dly_to_send_nack    inside {[1:max_dly_to_send_nack]}; }
  constraint dly_to_send_stop_c    { dly_to_send_stop    inside {[1:max_dly_to_send_stop]}; }
  constraint dly_to_send_rd_data_c { dly_to_send_rd_data inside {[1:max_dly_to_send_rd_data]}; }

  `uvm_object_utils_begin(i2c_agent_cfg)
    `uvm_field_int(is_active,        UVM_DEFAULT)
    `uvm_field_int(en_cov,           UVM_DEFAULT)
    `uvm_field_int(en_rx_checks,     UVM_DEFAULT)
    `uvm_field_int(en_tx_checks,     UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : i2c_agent_cfg
