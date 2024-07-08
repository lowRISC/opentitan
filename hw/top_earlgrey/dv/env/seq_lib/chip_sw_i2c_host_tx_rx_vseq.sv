// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stimulus vseq for testing the I2C Controller-mode module at a chip level
//
// - The SW test will program the DUT-I2C block into host mode, and then configure a
//   write-transfer with some randomly-generated data.
// - The I2C_Agent is configured to run an 'autoresponder' sequence (i2c_device_response_seq),
//   which accepts all write transfers, and returns the same data in read transfers.
// - SW will configure a read-transfer, and check it reads back the same data as was written as
//   part of the write-transfer.
//
// The logic in this vseq is mostly to configure the i2c_agent with an appropriate set of timing
// parameters, and then to start the autoresponder sequence.
//
class chip_sw_i2c_host_tx_rx_vseq extends chip_sw_i2c_tx_rx_vseq;

  ///////////////
  // VARIABLES //
  ///////////////

  rand int i2c_idx;

  `uvm_object_utils_begin(chip_sw_i2c_host_tx_rx_vseq)
    `uvm_field_int(i2c_idx, UVM_DEFAULT | UVM_DEC)
  `uvm_object_utils_end

  `uvm_object_new

  /////////////////
  // CONSTRAINTS //
  /////////////////

  constraint i2c_idx_c {
    i2c_idx inside {[0 : NUM_I2CS-1]};
  }

  /////////////
  // METHODS //
  /////////////

  // Override the base-class impl to pass software backdoor symbols that configure the DUT via SW.
  // - The I2C peripheral instance to test is selected via the plusarg '+i2c_idx'
  // - The timing parameters are taken from static values inherited from 'chip_sw_i2c_tx_rx_vseq'
  virtual task cpu_init();
    bit[7:0] clock_period_nanos_arr[1] = {clock_period_nanos};
    bit[7:0] rise_fall_nanos_arr[1] = {rise_fall_nanos};
    bit[7:0] i2c_clock_period_nanos_arr[4] = {<<byte{i2c_clock_period_nanos}};
    bit[7:0] i2c_idx_arr[1];
    bit[7:0] i2c_cdc_enabled_arr[1];

    void'($value$plusargs("i2c_idx=%0d", i2c_idx));
    `DV_CHECK(i2c_idx inside {[0 : NUM_I2CS-1]})
    i2c_idx_arr = {i2c_idx};

    super.cpu_init();

    // Pass the symbols to test software via the backdoor

    sw_symbol_backdoor_overwrite("kClockPeriodNanos", clock_period_nanos_arr);
    sw_symbol_backdoor_overwrite("kI2cRiseFallNanos", rise_fall_nanos_arr);
    sw_symbol_backdoor_overwrite("kI2cClockPeriodNanos", i2c_clock_period_nanos_arr);
    sw_symbol_backdoor_overwrite("kI2cIdx", i2c_idx_arr);
    if (cfg.en_dv_cdc) begin
      i2c_cdc_enabled_arr = {8'd1};
      sw_symbol_backdoor_overwrite("kI2cCdcInstrumentationEnabled", i2c_cdc_enabled_arr);
    end
  endtask


  virtual function void configure_agent_timing_cfg();

    // tClockLow needs to be "slightly" shorter than the actual clock low period
    // After fixing #15003, the clock low needs to be shortened by 1 additional cycle
    // to account for delayed output. The ClockLow value is not used to program
    // the DUT, but instead is used by the i2c agent to simulate when it should begin
    // driving data.  The i2c agent drives data as late as possible.
    int tSetupBit = 2;
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

  endfunction : configure_agent_timing_cfg


  virtual task body();
    super.body();

    // Enable the appropriate i2c_monitor
    cfg.m_i2c_agent_cfgs[i2c_idx].en_monitor = 1'b1;
    cfg.m_i2c_agent_cfgs[i2c_idx].if_mode = Device;

    // Enable the appropriate interface inside the chip_if
    cfg.chip_vif.enable_i2c(.inst_num(i2c_idx), .enable(1));

    // Configure the I2C Agent with an appropriate set of timing parameters to drive the stimulus.
    configure_agent_timing_cfg();

    `uvm_info(`gfn, $sformatf("Test vseq properties:\n%s", this.sprint()), UVM_MEDIUM)
    print_i2c_timing_cfg(i2c_idx);

    // Start the i2c_agent sequence which accepts all write and read transactions, and returns the
    // same data bytes when read that were previously written.
    i2c_device_autoresponder();
  endtask

  virtual task i2c_device_autoresponder();
    i2c_device_response_seq seq = i2c_device_response_seq::type_id::create("seq");
    fork seq.start(p_sequencer.i2c_sequencer_hs[i2c_idx]); join_none
  endtask


endclass : chip_sw_i2c_host_tx_rx_vseq
