// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
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
    .intr_debug_cable_o(interrupts[ADC_CTRL_INTERRUPT_INDEX]),
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

  `ASSERT(ChannelSelOnehot_A, (adc_o.channel_sel != 0) -> $onehot(adc_o.channel_sel), clk_aon,
          ~rst_aon_n)
  `ASSERT_KNOWN(ChannelSelKnown_A, adc_o.channel_sel, clk_aon, ~rst_aon_n)
  `ASSERT_KNOWN(PdKnown_A, adc_o.pd, clk_aon, ~rst_aon_n)


endmodule


