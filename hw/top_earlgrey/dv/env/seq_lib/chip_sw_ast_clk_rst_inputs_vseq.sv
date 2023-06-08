// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_ast_clk_rst_inputs_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_ast_clk_rst_inputs_vseq)

  `uvm_object_new

  localparam string ADC_CHANNEL_OUT_HDL_PATH = "tb.dut.u_ast.adc_d_o[9:0]";
  localparam string ADC_CHANNEL_IN_SEL_HDL_PATH = "tb.dut.u_ast.adc_chnsel_i[1:0]";

  localparam string ADC_DATA_VALID = "tb.dut.u_ast.adc_d_val_o";
  localparam string ADC_POWERDOWN = "tb.dut.u_ast.adc_pd_i";
  localparam string ADC_CTRL_WAKEUP_REQ = "tb.dut.top_earlgrey.u_pwrmgr_aon.wakeups_i[1]";
  localparam uint NUM_ADC_CHANNELS = 2;
  localparam uint NUM_LOW_POWER_SAMPLES = 3;
  localparam uint NUM_NORMAL_POWER_SAMPLES = 3;
  localparam uint WAKE_UP_TIME_IN_US = 80;
  localparam uint CHANNEL0_MIN = 128;
  localparam uint CHANNEL0_MAX = CHANNEL0_MIN + 127;
  localparam uint CHANNEL1_MIN = 512;
  localparam uint CHANNEL1_MAX = CHANNEL1_MIN + 127;

  localparam bit IN_RANGE = 1;
  localparam bit NOT_IN_RANGE = 0;

  event adc_valid_falling_edge_event;
  event adc_valid_rising_edge_event;
  event adc_channel1_event;

  bit   powerdown_count_enabled;
  int   powerdown_count;

  bit [9:0] channel0_data;
  bit [9:0] channel1_data;

  virtual task check_hdl_paths();
    int retval;
    retval = uvm_hdl_check_path(ADC_CHANNEL_OUT_HDL_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", ADC_CHANNEL_OUT_HDL_PATH))
    retval = uvm_hdl_check_path(ADC_CHANNEL_IN_SEL_HDL_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", ADC_CHANNEL_IN_SEL_HDL_PATH))
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
    symbol_byte_write("kWakeUpTimeInUs", WAKE_UP_TIME_IN_US);
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
      adc_data_valid=cfg.chip_vif.adc_data_valid;
      if (adc_data_valid_last_value == 1 && adc_data_valid == 0) begin
        ->adc_valid_falling_edge_event;
      end
      else if (adc_data_valid_last_value == 0 && adc_data_valid == 1) begin
        ->adc_valid_rising_edge_event;
      end
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask

  virtual task wait_for_adc_channel();
    bit [1:0] adc_channel;
    bit [1:0] adc_channel_valid_last_value;
    forever begin
      adc_channel_valid_last_value = adc_channel;
      `DV_CHECK(uvm_hdl_read(ADC_CHANNEL_IN_SEL_HDL_PATH, adc_channel));
      if (adc_channel_valid_last_value != 1 && adc_channel == 1) begin
        ->adc_channel1_event;
      end
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask

  virtual task force_adc_channels(input bit channel_idx,
                                  input bit channel_in_range);
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
    `DV_CHECK(uvm_hdl_force(ADC_CHANNEL_OUT_HDL_PATH, (channel_idx?channel1_data:channel0_data)));
  endtask

  virtual task generate_adc_data();
    @(adc_channel1_event);
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

    // Fork tasks for detecting edges.
    powerdown_count = 0;
    powerdown_count_enabled = 1;
    fork
      wait_for_adc_valid_falling_edge();
      wait_for_adc_channel();
    join_none
      //force adc digital data for test alert/rng after Deep sleep
      generate_adc_data();

      //force adc digital data for test alert/rng after regular sleep (io clk & core clk enabled)
      `DV_WAIT(cfg.sw_logger_vif.printed_log =="force new adc conv set")
      generate_adc_data();

      //force adc digital data for test alert/rng after regular sleep (all clk disabled)
      `DV_WAIT(cfg.sw_logger_vif.printed_log =="force new adc conv set")
      generate_adc_data();

    disable fork;

    `DV_WAIT(cfg.sw_logger_vif.printed_log =="c code is finished")

  endtask

endclass
