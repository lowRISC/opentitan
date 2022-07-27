// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// Enhanced DV_ASSERT_CTRL which kills active assertions before disabling them
`ifndef ADC_CTRL_DV_ASSERT_CTRL
`define ADC_CTRL_DV_ASSERT_CTRL(LABEL_, HIER_, LEVELS_ = 0, SCOPE_ = "", ID_ = $sformatf("%m")) \
  initial begin \
    bit assert_en; \
    forever begin \
      uvm_config_db#(bit)::wait_modified(null, SCOPE_, LABEL_); \
      if (!uvm_config_db#(bit)::get(null, SCOPE_, LABEL_, assert_en)) begin \
        `uvm_fatal(ID_, $sformatf("Failed to get \"%0s\" from uvm_config_db", LABEL_)) \
      end \
      if (assert_en) begin \
        `uvm_info(ID_, $sformatf("Enabling assertions: %0s", `DV_STRINGIFY(HIER_)), UVM_LOW) \
        $asserton(LEVELS_, HIER_); \
      end else begin \
        `uvm_info(ID_, $sformatf("Disabling assertions: %0s", `DV_STRINGIFY(HIER_)), UVM_LOW) \
        $assertkill(LEVELS_, HIER_); \
        $assertoff(LEVELS_, HIER_); \
      end \
    end \
  end
`endif


module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;

  import adc_ctrl_env_pkg::*;
  import adc_ctrl_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  `include "prim_assert.sv"

  wire clk, rst_n;
  wire clk_aon, rst_aon_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire wakeup_req;
  wire [ADC_CTRL_CHANNELS - 1 : 0] adc_channel_sel, adc_data_valid;
  logic [ADC_CTRL_CHANNELS - 1 : 0] adc_if_reqs;
  wire [ADC_CTRL_CHANNELS - 1 : 0][ADC_CTRL_DATA_WIDTH - 1 : 0] adc_data;
  wire ast_pkg::adc_ast_req_t adc_o;
  ast_pkg::adc_ast_rsp_t adc_i;
  adc_ctrl_env_cfg cfg;
  // Basic testing mode
  adc_ctrl_testmode_e cfg_testmode;
  // Auxiliary logic to time power up -> first channel request
  int pwrup_time, cfg_pwrup_time;
  bit pwrup_time_en;
  // Auxiliary logic to time power down -> power up
  int wakeup_time, cfg_wakeup_time;
  bit   wakeup_time_en;
  logic pd_prev;
  bit   cfg_lp_mode;

  `DV_ALERT_IF_CONNECT

  // interfaces
  clk_rst_if clk_rst_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  clk_rst_if clk_aon_rst_if (
    .clk  (clk_aon),
    .rst_n(rst_aon_n)
  );
  pins_if #(NUM_MAX_INTERRUPTS) intr_if (interrupts);
  pins_if #(1) wakeup_if (wakeup_req);
  pins_if #(1) devmode_if (devmode);
  tl_if tl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );

  // Array of push pull interfaces, one per ADC channel
  push_pull_if #(
    .DeviceDataWidth(ADC_CTRL_DATA_WIDTH)
  ) adc_if[ADC_CTRL_CHANNELS] (
    .clk  (clk_aon),
    .rst_n(rst_aon_n)
  );

  // dut
  adc_ctrl dut (
    .clk_i             (clk),
    .rst_ni            (rst_n),
    .clk_aon_i         (clk_aon),
    .rst_aon_ni        (rst_aon_n),
    .tl_i              (tl_if.h2d),
    .tl_o              (tl_if.d2h),
    .alert_rx_i        (alert_rx),
    .alert_tx_o        (alert_tx),
    .adc_o             (adc_o),
    .adc_i             (adc_i),
    .intr_match_done_o (interrupts[ADC_CTRL_INTERRUPT_INDEX]),
    .wkup_req_o        (wakeup_req)
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_aon_rst_if.set_active();
    clk_rst_if.set_active();
    clk_aon_rst_if.set_freq_khz(200);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_aon_rst_vif", clk_aon_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(wakeup_vif_t)::set(null, "*.env", "wakeup_vif", wakeup_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  initial begin
    #1ps;
    if (!uvm_config_db#(adc_ctrl_env_cfg)::get(
            null, "uvm_test_top.env", "cfg", cfg
        ) || cfg == null) begin
      `uvm_fatal("TB", "Couldn't find the environment config")
    end
    `uvm_info("TB", "Found environment config", UVM_MEDIUM)

    // Constantly update from configuration object
    forever begin
      cfg_testmode = cfg.testmode;
      cfg_pwrup_time = cfg.pwrup_time;
      cfg_wakeup_time = cfg.wakeup_time;
      cfg_lp_mode = cfg.lp_mode;
      @(cfg.pwrup_time or cfg.wakeup_time or cfg.testmode or cfg.lp_mode);
    end
  end

  // Push pull agents
  // Need to use generate loop as idx must be an elaborataion time constant
  for (genvar idx = 0; idx < ADC_CTRL_CHANNELS; idx++) begin : g_adc_if_connections
    initial begin
      uvm_config_db#(adc_push_pull_vif_t)::set(null, $sformatf("*env.m_adc_push_pull_agent_%0d", idx
                                               ), "vif", adc_if[idx]);
    end

    // Assign inputs and outputs

    // Convert data valid and data into a packed arrays for the Mux below.
    assign adc_data_valid[idx] = adc_if[idx].ack;
    assign adc_data[idx]       = adc_if[idx].d_data;

    // Connect requests
    //assign adc_if[idx].req = adc_o.channel_sel[idx] & ~adc_o.pd;
    assign adc_if[idx].req     = adc_if_reqs[idx];
  end

  // Output decode
  // We assert an adc_if request if:
  // 1. The coresponding channel is selected
  // 2. Power Down is not asserted
  // 3. No other channel has an acknowledge
  always_comb begin : adc_o_decode
    // default all off
    adc_if_reqs = 0;
    for (int idx = 0; idx < ADC_CTRL_CHANNELS; idx++) begin
      if (adc_o.channel_sel[idx] === 1 && adc_o.pd === 0) begin
        adc_if_reqs[idx] = 1;
        // Check no ack from another channel
        for (int idx_1 = 0; idx_1 < ADC_CTRL_CHANNELS; idx_1++) begin
          if (adc_data_valid[idx_1] === 1 && (idx_1 != idx)) adc_if_reqs[idx] = 0;
        end
      end
    end
  end

  // Input mux
  always_comb begin : adc_i_mux
    // Just or the valids
    adc_i.data_valid = |adc_data_valid;
    adc_i.data       = 'X;
    if (adc_o.pd === 0) begin
      // Only if power down deasserted
      for (int idx = 0; idx < ADC_CTRL_CHANNELS; idx++) begin
        if (adc_data_valid[idx] === 1) begin
          //adc_i.data_valid = adc_data_valid[idx];
          adc_i.data = adc_data[idx];
          break;
        end
      end
    end
  end

  // Auxiliary logic to time clocks since power down deasserted
  always @(posedge clk_aon or negedge rst_aon_n) begin
    if (!rst_aon_n) begin
      pwrup_time <= 0;
      pwrup_time_en <= 1;
    end else begin
      if (adc_o.pd == 1) begin
        pwrup_time <= 0;
        pwrup_time_en <= 1;
      end else begin
        if (|adc_o.channel_sel) pwrup_time_en <= 0;
        else if (pwrup_time_en) pwrup_time <= pwrup_time + 1;
      end
    end
  end
  // Pulse to check power up counter
  wire pwrup_time_chk = |adc_o.channel_sel & pwrup_time_en;

  // Auxiliary logic to time clocks from power down to power up
  always @(posedge clk_aon or negedge rst_aon_n) begin
    if (!rst_aon_n) begin
      wakeup_time <= 0;
      wakeup_time_en <= 0;
      pd_prev <= 0;
    end else begin
      if (adc_o.pd & ~pd_prev) begin
        // Positive edge on adc_o.pd begin counting wakeup time
        wakeup_time <= 0;
        wakeup_time_en <= 1;
      end else if (~adc_o.pd & pd_prev) begin
        // Negative edge on adc_o.pd stop counting wakeup time
        wakeup_time_en <= 0;
      end else if (wakeup_time_en) begin
        wakeup_time <= wakeup_time + 1;
      end
      // Delay PD for edge detect
      pd_prev <= adc_o.pd;
    end
  end
  // Pulse to check wake up counter
  wire wakeup_time_chk = ~adc_o.pd & pd_prev;
  // Model expects RTL to be in low power mode.
  wire testmode_low_power = cfg_testmode inside {AdcCtrlTestmodeLowpower} && cfg_lp_mode;

  // Check the DUT enters low power
  // In low power test mode, after falling edges on power down
  // and the last ADC channel select, power down should be re-asserted within 10 clock cycles
  //verilog_format: off - avoid bad formatting
  property EnterLowPower_P;
    first_match($fell(adc_o.pd) ##[+] $fell(adc_o.channel_sel[ADC_CTRL_CHANNELS - 1])) |=>
        ##[0:3] adc_o.pd;
  endproperty
  //verilog_format: on

  // Assertions
  `ASSERT(ChannelSelOnehot_A, $onehot0(adc_o.channel_sel), clk_aon, ~rst_aon_n)
  `ASSERT_KNOWN(ChannelSelKnown_A, adc_o.channel_sel, clk_aon, ~rst_aon_n)
  `ASSERT_KNOWN(PdKnown_A, adc_o.pd, clk_aon, ~rst_aon_n)
  `ASSERT(PwrupTime_A, $rose(pwrup_time_chk) |-> pwrup_time == (cfg_pwrup_time + 1), clk_aon,
          ~rst_aon_n)
  `ASSERT(WakeupTime_A, $rose(wakeup_time_chk) |-> wakeup_time == cfg_wakeup_time, clk_aon,
          ~rst_aon_n)
  `ASSERT(EnterLowPower_A, EnterLowPower_P, clk_aon, ~rst_aon_n | ~testmode_low_power)


  // Assertion controls
  `ADC_CTRL_DV_ASSERT_CTRL("ADC_IF_A_CTRL", adc_if[0])
  `ADC_CTRL_DV_ASSERT_CTRL("ADC_IF_A_CTRL", adc_if[1])
  `DV_ASSERT_CTRL("PwrupTime_A_CTRL", PwrupTime_A)
  `DV_ASSERT_CTRL("WakeupTime_A_CTRL", WakeupTime_A)
  `DV_ASSERT_CTRL("EnterLowPower_A_CTRL", EnterLowPower_A)
  `DV_ASSERT_CTRL("ADC_CTRL_FSM_A_CTRL", dut.u_adc_ctrl_core.u_adc_ctrl_fsm)

endmodule
