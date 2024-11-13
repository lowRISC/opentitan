// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// System verilog assertions for the adc_ctrl_fsm module

interface adc_ctrl_sva_if
  import uvm_pkg::*;
  import adc_ctrl_pkg::*;
  import adc_ctrl_env_pkg::*;
(
  input clk_i,      // regular core clock for SW config interface
  input clk_aon_i,  // always-on slow clock for internal logic
  input rst_ni,     // power-on hardware reset
  input rst_aon_ni, // power-on reset for the 200KHz clock(logic)
  input ast_pkg::adc_ast_req_t adc_o
);

  int pwrup_time;
  bit pwrup_time_en;
  int wakeup_time;
  bit wakeup_time_en;
  logic pd_prev;

  adc_ctrl_env_cfg cfg;
  adc_ctrl_testmode_e cfg_testmode;
  int cfg_pwrup_time;
  int cfg_wakeup_time;
  bit cfg_lp_mode;

`ifdef INC_ASSERT

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

  // Auxiliary logic to time clocks since power down deasserted
  always @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
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
  always @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
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
`endif

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
  `ASSERT(ChannelSelOnehot_A, $onehot0(adc_o.channel_sel), clk_aon_i, ~rst_aon_ni)
  `ASSERT_KNOWN(ChannelSelKnown_A, adc_o.channel_sel, clk_aon_i, ~rst_aon_ni)
  `ASSERT_KNOWN(PdKnown_A, adc_o.pd, clk_aon_i, ~rst_aon_ni)
  `ASSERT(PwrupTime_A, $rose(pwrup_time_chk) |-> pwrup_time == (cfg_pwrup_time + 1), clk_aon_i,
          ~rst_aon_ni)
  `ASSERT(WakeupTime_A, $rose(wakeup_time_chk) |-> wakeup_time == cfg_wakeup_time, clk_aon_i,
          ~rst_aon_ni)
  `ASSERT(EnterLowPower_A, EnterLowPower_P, clk_aon_i, ~rst_aon_ni | ~testmode_low_power)

  // Assertion controls

  `DV_ASSERT_CTRL("PwrupTime_A_CTRL", PwrupTime_A)
  `DV_ASSERT_CTRL("WakeupTime_A_CTRL", WakeupTime_A)
  `DV_ASSERT_CTRL("EnterLowPower_A_CTRL", EnterLowPower_A)
  `DV_ASSERT_CTRL("ADC_CTRL_FSM_A_CTRL", dut.u_adc_ctrl_core.u_adc_ctrl_fsm)

endinterface : adc_ctrl_sva_if
