// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_i2c_host_tx_rx_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_i2c_host_tx_rx_vseq)

  `uvm_object_new

  rand int i2c_idx;

  // TODO: Randomize this variable later when C side is ready.
  // When this is randomized, the sequence will arbitrarily pick one of the i2c interfaces
  // to test.
  constraint i2c_idx_c {
    i2c_idx inside {[0:0]};
  }

  // need to figure out is there a way to get this from the tb
  int clock_period_nanos = 41;
  int i2c_clock_period_nanos = 1000;
  int rise_fall_nanos = 10;
  int rise_cycles = ((rise_fall_nanos - 1) / clock_period_nanos) + 1;
  int fall_cycles = ((rise_fall_nanos - 1) / clock_period_nanos) + 1;
  int clock_period_cycles = ((i2c_clock_period_nanos - 1) / clock_period_nanos) + 1;
  int half_period_cycles = ((i2c_clock_period_nanos/2 - 1) / clock_period_nanos) + 1;

  virtual task cpu_init();
    bit[7:0] clock_period_nanos_data[1] = {clock_period_nanos};
    bit[7:0] rise_fall_nanos_data[1] = {rise_fall_nanos};
    bit[7:0] i2c_clock_period_nanos_data[4] = {<<byte{i2c_clock_period_nanos}};

    super.cpu_init();
    // need to figure out a better way to calculate this based on tb clock frequency
    sw_symbol_backdoor_overwrite("kClockPeriodNanos", clock_period_nanos_data);
    sw_symbol_backdoor_overwrite("kI2cRiseFallNanos", rise_fall_nanos_data);
    sw_symbol_backdoor_overwrite("kI2cClockPeriodNanos", i2c_clock_period_nanos_data);
  endtask

  virtual task body();
    super.body();

    // enable the monitor
    cfg.m_i2c_agent_cfgs[i2c_idx].en_monitor = 1'b1;
    cfg.m_i2c_agent_cfgs[i2c_idx].if_mode = Device;

    // Enbale appropriate interface
    cfg.chip_vif.enable_i2c(.inst_num(i2c_idx), .enable(1));

    `uvm_info(`gfn, $sformatf("Full period cycle: %d", clock_period_cycles), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("Half period cycle: %d", half_period_cycles), UVM_MEDIUM)

    // tClockLow needs to be "slightly" shorter than the actual clock low period
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockLow = half_period_cycles - 1;

    // tClockPulse needs to be "slightly" longer than the clock period.
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockPulse = half_period_cycles + 1;

    i2c_device_autoresponder();
  endtask

  virtual task i2c_device_autoresponder(i2c_device_response_seq seq = null);
    if (seq == null) seq = i2c_device_response_seq::type_id::create("seq");
    fork seq.start(p_sequencer.i2c_sequencer_hs[i2c_idx]); join_none
    #0;  // Ensure seq actually starts before subsequent code executes.
  endtask


endclass : chip_sw_i2c_host_tx_rx_vseq
