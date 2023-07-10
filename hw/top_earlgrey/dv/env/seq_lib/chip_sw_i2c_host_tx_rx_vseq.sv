// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_i2c_host_tx_rx_vseq extends chip_sw_i2c_tx_rx_vseq;
  `uvm_object_utils(chip_sw_i2c_host_tx_rx_vseq)

  `uvm_object_new

  rand int i2c_idx;
  constraint i2c_idx_c {
    i2c_idx inside {[0:NUM_I2CS-1]};
  }

  virtual task cpu_init();
    bit[7:0] clock_period_nanos_arr[1] = {clock_period_nanos};
    bit[7:0] rise_fall_nanos_arr[1] = {rise_fall_nanos};
    bit[7:0] i2c_clock_period_nanos_arr[4] = {<<byte{i2c_clock_period_nanos}};
    bit[7:0] i2c_idx_arr[1];
    bit[7:0] i2c_cdc_enabled_arr[1];

    void'($value$plusargs("i2c_idx=%0d", i2c_idx));
    `DV_CHECK(i2c_idx inside {[0:NUM_I2CS-1]})

    i2c_idx_arr = {i2c_idx};
    super.cpu_init();
    // need to figure out a better way to calculate this based on tb clock frequency
    sw_symbol_backdoor_overwrite("kClockPeriodNanos", clock_period_nanos_arr);
    sw_symbol_backdoor_overwrite("kI2cRiseFallNanos", rise_fall_nanos_arr);
    sw_symbol_backdoor_overwrite("kI2cClockPeriodNanos", i2c_clock_period_nanos_arr);
    sw_symbol_backdoor_overwrite("kI2cIdx", i2c_idx_arr);
    if (cfg.en_dv_cdc) begin
      i2c_cdc_enabled_arr = {8'd1};
      sw_symbol_backdoor_overwrite("kI2cCdcInstrumentationEnabled", i2c_cdc_enabled_arr);
    end
  endtask

  virtual task body();
    int tSetupBit;
    super.body();

    // enable the monitor
    cfg.m_i2c_agent_cfgs[i2c_idx].en_monitor = 1'b1;
    cfg.m_i2c_agent_cfgs[i2c_idx].if_mode = Device;

    // Enbale appropriate interface
    cfg.chip_vif.enable_i2c(.inst_num(i2c_idx), .enable(1));

    `uvm_info(`gfn, $sformatf("Full period cycle: %d", clock_period_cycles), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("Half period cycle: %d", half_period_cycles), UVM_MEDIUM)

    // tClockLow needs to be "slightly" shorter than the actual clock low period
    // After fixing #15003, the clock low needs to be shortened by 1 additional cycle
    // to account for delayed output. The ClockLow value is not used to program
    // the DUT, but instead is used by the i2c agent to simulate when it should begin
    // driving data.  The i2c agent drives data as late as possible.
    tSetupBit = 2;
    // Nullify the CDC instrumentation delays on the input synchronizers,
    // since SDA never truly changes simultaneously with SCL. Their happening
    // on the same cycle in simulation is due to time/cycle quantization.
    // Drive SDA a cycle early to account for CDC delays, if CDC is enabled.
    // Hold SDA a cycle longer to account for CDC delays, if CDC is enabled.
    if (cfg.en_dv_cdc) begin
      tSetupBit++;
      cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tHoldBit = 1;
    end
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tSetupBit = tSetupBit;
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockLow = half_period_cycles - tSetupBit;
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockPulse = half_period_cycles;

    print_i2c_timing_cfg(i2c_idx);
    i2c_device_autoresponder();
  endtask

  virtual task i2c_device_autoresponder();
    i2c_device_response_seq seq = i2c_device_response_seq::type_id::create("seq");
    fork seq.start(p_sequencer.i2c_sequencer_hs[i2c_idx]); join_none
  endtask


endclass : chip_sw_i2c_host_tx_rx_vseq
