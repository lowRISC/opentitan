// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_adc_ctrl_sleep_debug_cable_wakeup_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_adc_ctrl_sleep_debug_cable_wakeup_vseq)

  `uvm_object_new

  localparam string ADC_CHANNEL_OUT_HDL_PATH = "tb.dut.u_ast.adc_d_o[9:0]";
  localparam string ADC_DATA_VALID = "tb.dut.u_ast.adc_d_val_o";
  localparam string ADC_POWERDOWN = "tb.dut.u_ast.adc_pd_i";

  localparam string ADC_CTRL_WAKEUP_REQ = "tb.dut.top_earlgrey.u_pwrmgr_aon.wakeups_i[1]";

  localparam uint NUM_ADC_CHANNELS = 2;
  localparam uint NUM_LOW_POWER_SAMPLES = 8;
  localparam uint NUM_NORMAL_POWER_SAMPLES = 8;
  localparam uint WAKE_UP_TIME_AON_CYCLES = 16;
  localparam uint CHANNEL0_MIN = 128;
  localparam uint CHANNEL0_MAX = CHANNEL0_MIN + 127;
  localparam uint CHANNEL1_MIN = 512;
  localparam uint CHANNEL1_MAX = CHANNEL1_MIN + 127;

  localparam bit IN_RANGE = 1;
  localparam bit NOT_IN_RANGE = 0;

  event adc_valid_falling_edge_event;
  event adc_valid_rising_edge_event;
  bit   powerdown_count_enabled;
  int   powerdown_count;

  bit [9:0] channel0_data;
  bit [9:0] channel1_data;

  virtual task check_hdl_paths();
    int retval;
    retval = uvm_hdl_check_path(ADC_CHANNEL_OUT_HDL_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", ADC_CHANNEL_OUT_HDL_PATH))
    retval = uvm_hdl_check_path(ADC_DATA_VALID);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", ADC_DATA_VALID))
    retval = uvm_hdl_check_path(ADC_POWERDOWN);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", ADC_POWERDOWN))
    retval = uvm_hdl_check_path(ADC_CTRL_WAKEUP_REQ);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", ADC_CTRL_WAKEUP_REQ))
  endtask

  virtual task symbol_byte_write(string str, bit [7:0] data);
    bit [7:0] array_data[1] = {data};
    sw_symbol_backdoor_overwrite(str, array_data);
  endtask

  virtual task cpu_init();
    // sw_symbol_backdoor_overwrite takes an array as the input.
    super.cpu_init();
    symbol_byte_write("kNumLowPowerSamples", NUM_LOW_POWER_SAMPLES);
    symbol_byte_write("kNumNormalPowerSamples", NUM_NORMAL_POWER_SAMPLES);
    symbol_byte_write("kWakeUpTimeAonCycles", WAKE_UP_TIME_AON_CYCLES);
    symbol_byte_write("kChannel0MaxLowByte", CHANNEL0_MAX[7:0]);
    symbol_byte_write("kChannel0MaxHighByte", CHANNEL0_MAX[15:8]);
    symbol_byte_write("kChannel0MinLowByte", CHANNEL0_MIN[7:0]);
    symbol_byte_write("kChannel0MinHighByte", CHANNEL0_MIN[15:8]);
    symbol_byte_write("kChannel1MaxLowByte", CHANNEL1_MAX[7:0]);
    symbol_byte_write("kChannel1MaxHighByte", CHANNEL1_MAX[15:8]);
    symbol_byte_write("kChannel1MinLowByte", CHANNEL1_MIN[7:0]);
    symbol_byte_write("kChannel1MinHighByte", CHANNEL1_MIN[15:8]);
  endtask

  virtual task wait_for_adc_valid_falling_edge();
    int retval;
    bit adc_data_valid;
    bit adc_data_valid_last_value;
    forever begin
      adc_data_valid_last_value = adc_data_valid;
      retval = uvm_hdl_read(ADC_DATA_VALID, adc_data_valid);
      `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", ADC_DATA_VALID))
      if (adc_data_valid_last_value == 1 && adc_data_valid == 0) begin
        ->adc_valid_falling_edge_event;
      end
      else if (adc_data_valid_last_value == 0 && adc_data_valid == 1) begin
        ->adc_valid_rising_edge_event; // force data_o when valid is asserted
      end
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask

  virtual task detect_powerdown_rising_edge();
    int retval;
    bit powerdown_value;
    bit powerdown_last_value;
    forever begin
      powerdown_last_value = powerdown_value;
      retval = uvm_hdl_read(ADC_POWERDOWN, powerdown_value);
      `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", ADC_POWERDOWN))
      if (powerdown_value == 1 && powerdown_last_value == 0) begin
        if (powerdown_count_enabled == 1) begin
          powerdown_count++;
        end
      end
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask

  virtual task force_adc_channels(input bit channel_idx,
                                  input bit channel_in_range,
                                  input bit force_old_data = 0);
    if (!force_old_data) begin
      if (channel_in_range == 1) begin
        if (channel_idx == 0) begin
          `DV_CHECK(std::randomize(channel0_data) with {
                    channel0_data inside {[CHANNEL0_MIN : CHANNEL0_MAX]};});
        end else begin
          `DV_CHECK(std::randomize(channel1_data) with {
                    channel1_data inside {[CHANNEL1_MIN : CHANNEL1_MAX]};});
        end
      end else begin
        if (channel_idx == 0) begin
          `DV_CHECK(std::randomize(channel0_data) with {
                    !{channel0_data inside {[CHANNEL0_MIN : CHANNEL0_MAX]}};});
        end else begin
          `DV_CHECK(std::randomize(channel1_data) with {
                    !{channel1_data inside {[CHANNEL1_MIN : CHANNEL1_MAX]}};});
        end
      end
    end
    `DV_CHECK(uvm_hdl_force(ADC_CHANNEL_OUT_HDL_PATH, (channel_idx?channel1_data:channel0_data)));
  endtask

  virtual task generate_adc_data();
    bit wakeup;
    int bad_sample;

    // Data with a channel 0 glitch.
    bad_sample = $urandom_range(0, NUM_LOW_POWER_SAMPLES - 1);
    for (int i = 0; i < NUM_LOW_POWER_SAMPLES; i++) begin
      @(adc_valid_rising_edge_event);
      if (i == bad_sample) begin
        force_adc_channels(0, NOT_IN_RANGE);
      end else begin
        force_adc_channels(0, IN_RANGE);
      end
      @(adc_valid_rising_edge_event);
      force_adc_channels(1, IN_RANGE);
    end

    // Both channels glitched.
    for (int idx = 0; idx < NUM_ADC_CHANNELS; idx++) begin
      @(adc_valid_rising_edge_event);
      force_adc_channels(idx, NOT_IN_RANGE);
    end

    // Data with a channel 1 glitch.
    bad_sample = $urandom_range(0, NUM_LOW_POWER_SAMPLES - 1);
    for (int i = 0; i < NUM_LOW_POWER_SAMPLES; i++) begin
      @(adc_valid_rising_edge_event);
      force_adc_channels(0, IN_RANGE);
      @(adc_valid_rising_edge_event);
      if (i == bad_sample) begin
        force_adc_channels(1, NOT_IN_RANGE);
      end else begin
        force_adc_channels(1, IN_RANGE);
      end
    end

    // Both channels glitched.
    for (int i = 0; i < NUM_NORMAL_POWER_SAMPLES; i++) begin
      for (int idx = 0; idx < NUM_ADC_CHANNELS; idx++) begin
        @(adc_valid_rising_edge_event);
        force_adc_channels(idx, NOT_IN_RANGE,(i>0?1:0));
      end
    end

    // Check that there is no unexpected wakeup and that there
    // has been a number of powerdown signals following the glitched data.
    `DV_CHECK(uvm_hdl_read(ADC_CTRL_WAKEUP_REQ, wakeup));
    `DV_CHECK_EQ_FATAL(wakeup, 0, "Unexpected wakeup.")
    `DV_CHECK(powerdown_count >= NUM_LOW_POWER_SAMPLES * 3);

    // Data with both channels in range which will trigger a wakeup.
    for (int i = 0; i < NUM_LOW_POWER_SAMPLES; i++) begin
      for (int idx = 0; idx < NUM_ADC_CHANNELS; idx++) begin
        @(adc_valid_rising_edge_event);
        force_adc_channels(idx, IN_RANGE);
      end
    end
    for (int i = 0; i < NUM_NORMAL_POWER_SAMPLES; i++) begin
      for (int idx = 0; idx < NUM_ADC_CHANNELS; idx++) begin
        @(adc_valid_rising_edge_event);
        force_adc_channels(idx, IN_RANGE);
      end
    end
  endtask

  virtual task body();
    check_hdl_paths();
    super.body();

    // Wait for test to enter WFI before generating ADC data which will
    // cause a wakeup event.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)

    // Fork tasks for detecting edges.
    powerdown_count = 0;
    powerdown_count_enabled = 1;
    fork begin : isolation_fork
      fork
        wait_for_adc_valid_falling_edge();
        detect_powerdown_rising_edge();
      join_none

      // Generate a sequence of ADC data.
      generate_adc_data();

      disable fork;
    end join
  endtask

endclass
