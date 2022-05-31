// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_adc_ctrl_sleep_debug_cable_wakeup_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_adc_ctrl_sleep_debug_cable_wakeup_vseq)

  `uvm_object_new

  localparam string ADC_CHANNEL0_HDL_PATH = "tb.dut.u_ast.u_adc.u_adc_ana.adc_d_ch0_o";
  localparam string ADC_CHANNEL1_HDL_PATH = "tb.dut.u_ast.u_adc.u_adc_ana.adc_d_ch1_o";
  localparam string ADC_DATA_VALID = "tb.dut.u_ast.u_adc.adc_d_val_o";
  localparam string ADC_POWERDOWN = "tb.dut.u_ast.u_adc.adc_pd_i";
  localparam string ADC_CTRL_WAKEUP_REQ = "tb.dut.top_earlgrey.u_pwrmgr_aon.wakeups_i[1]";

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
  bit   powerdown_count_enabled;
  int   powerdown_count;

  virtual task check_hdl_paths();
    int retval;
    retval = uvm_hdl_check_path(ADC_CHANNEL0_HDL_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", ADC_CHANNEL0_HDL_PATH))
    retval = uvm_hdl_check_path(ADC_CHANNEL1_HDL_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", ADC_CHANNEL1_HDL_PATH))
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

  virtual task force_adc_channels(input bit channel0_in_range, input bit channel1_in_range);
    bit [9:0] channel0_data;
    bit [9:0] channel1_data;
    if (channel0_in_range == 1) begin
      `DV_CHECK(std::randomize(channel0_data) with {
                channel0_data inside {[CHANNEL0_MIN : CHANNEL0_MAX]};});
    end else begin
      `DV_CHECK(std::randomize(channel0_data) with {
                !{channel0_data inside {[CHANNEL0_MIN : CHANNEL0_MAX]}};});
    end
    `DV_CHECK(uvm_hdl_force(ADC_CHANNEL0_HDL_PATH, channel0_data));
    if (channel1_in_range == 1) begin
      `DV_CHECK(std::randomize(channel1_data) with {
                channel1_data inside {[CHANNEL1_MIN : CHANNEL1_MAX]};});
    end else begin
      `DV_CHECK(std::randomize(channel1_data) with {
                !{channel1_data inside {[CHANNEL1_MIN : CHANNEL1_MAX]}};});
    end
    `DV_CHECK(uvm_hdl_force(ADC_CHANNEL1_HDL_PATH, channel1_data));
  endtask

  virtual task generate_adc_data();
    bit wakeup;
    int bad_sample;

    // Data with a channel 0 glitch.
    bad_sample = $urandom_range(0, NUM_LOW_POWER_SAMPLES - 1);
    for (int i = 0; i < NUM_LOW_POWER_SAMPLES; i++) begin
      if (i == bad_sample) begin
        force_adc_channels(NOT_IN_RANGE, IN_RANGE);
      end else begin
        force_adc_channels(IN_RANGE, IN_RANGE);
      end
      repeat (2) @(adc_valid_falling_edge_event);
    end

    // Both channels glitched.
    force_adc_channels(NOT_IN_RANGE, NOT_IN_RANGE);
    repeat (2) @(adc_valid_falling_edge_event);

    // Data with a channel 1 glitch.
    bad_sample = $urandom_range(0, NUM_LOW_POWER_SAMPLES - 1);
    for (int i = 0; i < NUM_LOW_POWER_SAMPLES; i++) begin
      if (i == bad_sample) begin
        force_adc_channels(IN_RANGE, NOT_IN_RANGE);
      end else begin
        force_adc_channels(IN_RANGE, IN_RANGE);
      end
      repeat (2) @(adc_valid_falling_edge_event);
    end

    // Both channels glitched.
    force_adc_channels(NOT_IN_RANGE, NOT_IN_RANGE);
    repeat (NUM_NORMAL_POWER_SAMPLES * 2) @(adc_valid_falling_edge_event);

    // Check that there is no unexpected wakeup and that there
    // has been a number of powerdown signals following the glitched data.
    `DV_CHECK(uvm_hdl_read(ADC_CTRL_WAKEUP_REQ, wakeup));
    `DV_CHECK_EQ_FATAL(wakeup, 0, "Unexpected wakeup.")
    `DV_CHECK(powerdown_count >= NUM_LOW_POWER_SAMPLES * 3);

    // Data with both channels in range which will trigger a wakeup.
    for (int i = 0; i < NUM_LOW_POWER_SAMPLES; i++) begin
      force_adc_channels(IN_RANGE, IN_RANGE);
      repeat (2) @(adc_valid_falling_edge_event);
    end
    for (int i = 0; i < NUM_NORMAL_POWER_SAMPLES; i++) begin
      force_adc_channels(IN_RANGE, IN_RANGE);
      repeat (2) @(adc_valid_falling_edge_event);
    end
  endtask

  virtual task body();
    check_hdl_paths();
    super.body();

    // Wait for test to enter WFI before generating ADC data which will
    // cause a wakeup event.
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi);

    // Fork tasks for detecting edges.
    powerdown_count = 0;
    powerdown_count_enabled = 1;
    fork
      wait_for_adc_valid_falling_edge();
      detect_powerdown_rising_edge();
    join_none

    // Generate a sequence of ADC data.
    generate_adc_data();

    disable fork;
  endtask

endclass
