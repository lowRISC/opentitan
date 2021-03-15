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

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;

  wire clk_core, rst_core_n;
  wire [pwm_reg_pkg::NOutputs-1:0] pwm;
  wire [pwm_reg_pkg::NOutputs-1:0] pwm_en;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  clk_rst_if clk_rst_core_if(.clk(clk_core), .rst_n(rst_core_n));
  pins_if #(1) devmode_if(devmode);
  pwm_if #(.NumChannels(pwm_reg_pkg::NOutputs)) pwm_if();
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  // dut
  pwm dut (
    .clk_i         (clk),
    .rst_ni        (rst_n),

    .clk_core_i    (clk_core),
    .rst_core_ni   (rst_core_n),

    .tl_i          (tl_if.h2d),
    .tl_o          (tl_if.d2h),

    .cio_pwm_o     (pwm),
    .cio_pwm_en_o  (pwm_en)
  );

  assign pwm_if.clk_core   = clk_core;
  assign pwm_if.rst_core_n = rst_core_n;
  assign pwm_if.pwm        = pwm;
  assign pwm_if.pwm_en     = pwm_en;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    clk_rst_core_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_core_vif", clk_rst_core_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual pwm_if)::set(null, "*.env.m_pwm_agent*", "vif", pwm_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
