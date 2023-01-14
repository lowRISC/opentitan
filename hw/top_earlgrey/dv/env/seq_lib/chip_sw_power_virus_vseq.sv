// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_power_virus_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_power_virus_vseq)

  `uvm_object_new

  virtual function int sw_symbol_backdoor_read32(string symbol);
    bit [7:0] byte_array[4];
    sw_symbol_backdoor_read(symbol, byte_array);
    return {<<byte{byte_array}};
  endfunction

  virtual task i2c_device_autoresponder(int i2c_idx);
    i2c_device_response_seq seq = i2c_device_response_seq::type_id::create("seq");
    fork seq.start(p_sequencer.i2c_sequencer_hs[i2c_idx]); join_none
  endtask

  virtual task body();
    bit [31:0] i2c_scl_period_ns;          // `kI2cSclPeriodNs` in SW
    bit [31:0] peripheral_clock_period_ns; // `peripheral_clock_period_ns` in SW
    bit [31:0] half_cycles_in_i2c_period;

    super.body();

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Computed peripheral clock period.");

    // Backdoor read I2C configuration parameters.
    i2c_scl_period_ns = sw_symbol_backdoor_read32("kI2cSclPeriodNs");
    peripheral_clock_period_ns = sw_symbol_backdoor_read32("peripheral_clock_period_ns");
    `uvm_info(`gfn, $sformatf("kI2cSclPeriodNs = %0d", i2c_scl_period_ns), UVM_LOW);
    `uvm_info(`gfn, $sformatf("peripheral_clock_period_ns = %0d", peripheral_clock_period_ns),
      UVM_LOW);

    half_cycles_in_i2c_period = ((int'(i2c_scl_period_ns) / 2 - 1) /
      int'(peripheral_clock_period_ns)) + 1;
    `uvm_info(`gfn, $sformatf("Half (peripheral) cycles in I2C clock period: %d",
      half_cycles_in_i2c_period), UVM_LOW);

    // Enable I2C monitors.
    foreach (cfg.m_i2c_agent_cfgs[i]) begin
      cfg.m_i2c_agent_cfgs[i].en_monitor = 1'b1;
      cfg.m_i2c_agent_cfgs[i].if_mode = Device;
      cfg.chip_vif.enable_i2c(.inst_num(i), .enable(1));
      cfg.m_i2c_agent_cfgs[i].timing_cfg.tClockLow = half_cycles_in_i2c_period - 2;
      cfg.m_i2c_agent_cfgs[i].timing_cfg.tClockPulse = half_cycles_in_i2c_period + 1;
      i2c_device_autoresponder(i);
    end

  endtask

endclass : chip_sw_power_virus_vseq
