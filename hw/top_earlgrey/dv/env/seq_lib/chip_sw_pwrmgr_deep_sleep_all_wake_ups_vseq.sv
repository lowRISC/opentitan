// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_pwrmgr_deep_sleep_all_wake_ups_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_pwrmgr_deep_sleep_all_wake_ups_vseq)
  `uvm_object_new

  localparam string ADC_CHANNEL_OUT_HDL_PATH = "tb.dut.u_ast.adc_d_o[9:0]";
  localparam string ADC_CHANNEL_IN_SEL_HDL_PATH = "tb.dut.u_ast.adc_chnsel_i[1:0]";

  event adc_valid_rising_edge_event;
  event adc_channel1_event;
  event release_adc_force;

  virtual task wait_for_adc_channel();
    bit [1:0] adc_channel;
    bit [1:0] adc_channel_valid_last_value;
    forever begin
      adc_channel_valid_last_value = adc_channel;
      `DV_CHECK(uvm_hdl_read(ADC_CHANNEL_IN_SEL_HDL_PATH, adc_channel));
      if ( adc_channel_valid_last_value != 1 && adc_channel == 1) begin
        ->adc_channel1_event;
      end
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask

  virtual task wait_for_adc_valid_falling_edge();
    bit adc_data_valid;
    bit adc_data_valid_last_value;
    forever begin
      adc_data_valid_last_value = adc_data_valid;
      adc_data_valid=cfg.chip_vif.adc_data_valid;
      if (adc_data_valid_last_value == 0 && adc_data_valid == 1) begin
        ->adc_valid_rising_edge_event;
      end
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask

  virtual task force_adc_channels(input bit [9:0] channel0_value,
                                  input bit [9:0] channel1_value);
    // sync with ADC channel1
    @(adc_channel1_event);
    fork : force_adc_channels
      begin
        forever begin
          // force ADC channel0,1
          @(adc_valid_rising_edge_event);
          `DV_CHECK(uvm_hdl_force(ADC_CHANNEL_OUT_HDL_PATH, (channel0_value)));
          @(adc_valid_rising_edge_event);
          `DV_CHECK(uvm_hdl_force(ADC_CHANNEL_OUT_HDL_PATH, (channel1_value)));
        end
      end
      begin
        // wait for release the adc force
        @(release_adc_force);
        disable force_adc_channels;
      end
    join_none;
  endtask

  virtual task pre_start();
    super.pre_start();
    cfg.chip_vif.pwrb_in_if.drive(1'b1); // off
  endtask

  virtual task body();
    uint timeout_long  = 10_000_000;
    uint timeout_short = 1_000_000;
    bit twice_each   = 0;
    int repeat_count = 1;
    super.body();

    fork
      wait_for_adc_valid_falling_edge();
      wait_for_adc_channel();
    join_none

    // Give the pin a default value.
    cfg.chip_vif.pinmux_wkup_if.set_pulldown_en(1'b1);

    if ($value$plusargs("do_random=%b", twice_each) && twice_each) begin
      repeat_count = 2;
    end

    // Need to use hard coded string.
    // Loop with sformatf %d doesn't work

    // Add sample number for the future reference.
    // This is sampled from sv simulation and can be varied
    // over test run as well as the version of design.
    // Total run time was 21ms.
    // @3.5ms
    repeat (repeat_count) begin
      `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Issue WFI to enter sleep 0");,
                   "Timed out waiting for enter sleep 0", timeout_long)
      wakeup_action(0);
      // @6.3ms
      `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Woke up by source 0");,
                   "Timed out waiting for Woke up by source 0", timeout_long)
      release_action(0);
    end
    // @6.45ms
    repeat (repeat_count) begin
      `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Issue WFI to enter sleep 1");,
                   "Timed out waiting for enter sleep 1", timeout_short)
      wakeup_action(1);
      // @12.28ms
      `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Woke up by source 1");,
                   "Timed out waiting for Woke up by source 1", timeout_long)
      release_action(1);
    end
    // @12.425
    repeat (repeat_count) begin
      `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Issue WFI to enter sleep 2");,
                   "Timed out waiting for enter sleep 2", timeout_short)
      wakeup_action(2);
      // @15.248
      `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Woke up by source 2");,
                   "Timed out waiting for Woke up by source 2", timeout_long)
      release_action(2);
    end
 endtask // body

  // Trigger wakeup signal for each test round
  // Round 0 : input for sysrst ctrl
  // Round 1 : input for adc ctrl (force)
  // Round 2 : input for pinmux wakeup detector
  task wakeup_action(int round);
     repeat(20) @(posedge cfg.ast_supply_vif.clk);
    case(round)
      0: begin
        `uvm_info(`gfn, "Push power button ", UVM_MEDIUM)
        cfg.chip_vif.pwrb_in_if.drive(1'b0); // on
      end
      1: begin
        `uvm_info(`gfn, "Force adc out ", UVM_MEDIUM)
        // Force to random positive value
        force_adc_channels(5,115);
      end
      2: begin
        `uvm_info(`gfn, "Send pattern to pinmux wakeup detector ", UVM_MEDIUM)
        cfg.chip_vif.pinmux_wkup_if.drive(1'b1);
      end
      default: `uvm_fatal(`gfn, $sformatf("round %d is not allowed", round))
    endcase
  endtask // wakeup_action

  // Release wakeup signals
  task release_action(int round);
    case(round)
      0: cfg.chip_vif.pwrb_in_if.drive(1'b1);
      1: begin
        `DV_CHECK(uvm_hdl_release(ADC_CHANNEL_OUT_HDL_PATH))
        ->release_adc_force;
      end
      2:     cfg.chip_vif.pinmux_wkup_if.drive(1'b0);
      default: `uvm_fatal(`gfn, $sformatf("round %d is not allowed", round))
    endcase
  endtask // release_action
endclass // chip_sw_pwrmgr_deep_sleep_all_wake_ups_vseq
