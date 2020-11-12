// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_agent_cfg extends dv_base_agent_cfg;

  bit en_rx_checks  = 1'b1; // enable RX checks (implemented in monitor)
  bit en_tx_checks  = 1'b1; // enable TX checks (implemented in monitor)
  bit en_rx_monitor = 1'b1; // enable RX monitor
  bit en_tx_monitor = 1'b1; // enable TX monitor

  // device specific cfg
  baud_rate_e baud_rate;
  bit en_parity;
  bit odd_parity;

  // Controls upto what percentage of the clock period the RX is randomly glitched every 1ns.
  // RX is glitched at the start of the clock to ensure that the design is robust enough to sample
  // the correct value (typically at the center of the clock). The recommended range for this value
  // is 0-10%.
  local uint uart_period_glitch_pct = 10;

  // Logger settings.
  bit en_logger           = 1'b0; // enable logger on tx
  bit use_rx_for_logger   = 1'b0; // use rx instead of tx
  string logger_id        = "uart_logger";
  bit write_logs_to_file  = 1'b1;

  // reset is controlled at upper seq-level as no reset pin on uart interface
  bit under_reset;

  // interface handle used by driver, monitor & the sequencer
  virtual uart_if vif;

  // The actual UART clock is not perfectly aligned to the baud rate. The clock btw transmitter and
  // receiver can have certain difference
  // driver is using perfect baud rate. Here is the max allowed clock drift for design comparing the
  // ideal baud rate, This number must be less than 50
  // if set 20 here, received data must be ready to sample and stable at 30%-70% of the cycle
  local uint max_drift_cycle_pct = 25;

  `uvm_object_utils_begin(uart_agent_cfg)
    `uvm_field_int(en_rx_checks,  UVM_DEFAULT)
    `uvm_field_int(en_tx_checks,  UVM_DEFAULT)
    `uvm_field_int(en_tx_monitor, UVM_DEFAULT)
    `uvm_field_int(en_rx_monitor, UVM_DEFAULT)
    `uvm_field_int(en_parity,     UVM_DEFAULT)
    `uvm_field_int(odd_parity,    UVM_DEFAULT)
    `uvm_field_enum(baud_rate_e, baud_rate, UVM_DEFAULT)
    `uvm_field_int(uart_period_glitch_pct, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  function void set_uart_period_glitch_pct(uint pct);
    `DV_CHECK_LT_FATAL(pct, 20)
    uart_period_glitch_pct = pct;
  endfunction

  function uint get_uart_period_glitch_pct();
    return uart_period_glitch_pct;
  endfunction

  function void set_baud_rate(baud_rate_e b);
    baud_rate = b;
    vif.uart_clk_period_ns = (get_baud_rate_period_ns(b) * 1ns);
  endfunction

  function void set_parity(bit en_parity, bit odd_parity);
    this.en_parity = en_parity;
    this.odd_parity = odd_parity;
  endfunction

  function void set_max_drift_cycle_pct(uint pct);
    `DV_CHECK_LT_FATAL(pct, 50)
    max_drift_cycle_pct = pct;
  endfunction

  function int get_max_drift_cycle_pct();
    return max_drift_cycle_pct;
  endfunction

  virtual function void reset_asserted();
    under_reset = 1;
  endfunction

  virtual function void reset_deasserted(bit re_enable_chk_mon = 1);
    under_reset = 0;
    vif.reset_uart_rx();
    if (re_enable_chk_mon) begin
      en_rx_checks  = 1;
      en_tx_checks  = 1;
      en_rx_monitor = 1;
      en_tx_monitor = 1;
    end
  endfunction

endclass
