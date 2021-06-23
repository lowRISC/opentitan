// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import pwm_env_pkg::*;
  import pwm_test_pkg::*;
  import pwm_monitor_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  localparam PWM_NUM_CHANNELS = pwm_reg_pkg::NOutputs;

  wire clk;
  wire rst_n;
  wire devmode;
  wire clk_core;
  wire rst_core_n;
  wire [PWM_NUM_CHANNELS-1:0] cio_pwm;
  wire [PWM_NUM_CHANNELS-1:0] cio_pwm_en;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  clk_rst_if clk_rst_core_if(.clk(clk_core), .rst_n(rst_core_n));
  pins_if #(1) devmode_if(devmode);
  pwm_if #(PWM_NUM_CHANNELS) pwm_if();
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  `DV_ALERT_IF_CONNECT

  // dut
  pwm dut (
    .clk_i         (clk),
    .rst_ni        (rst_n),

    .clk_core_i    (clk_core),
    .rst_core_ni   (rst_core_n),

    .tl_i          (tl_if.h2d),
    .tl_o          (tl_if.d2h),

    .alert_rx_i    (alert_rx   ),
    .alert_tx_o    (alert_tx   ),

    .cio_pwm_o     (cio_pwm),
    .cio_pwm_en_o  (cio_pwm_en)
  );

  assign pwm_if.clk   = clk_core;
  assign pwm_if.rst_n = rst_core_n;
  for (genvar i = 0; i < PWM_NUM_CHANNELS; i++) begin : gen_mux
    assign pwm_if.pwm[i] = (cio_pwm_en[i]) ? cio_pwm[i] : 1'b0;
  end

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    clk_rst_core_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_core_vif", clk_rst_core_if);
    uvm_config_db#(virtual pwm_if#(PWM_NUM_CHANNELS))
        ::set(null, "*.env.m_pwm_monitor*", "vif", pwm_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
