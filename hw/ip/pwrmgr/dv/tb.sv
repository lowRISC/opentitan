// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import pwrmgr_env_pkg::*;
  import pwrmgr_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire clk_slow, rst_slow_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  clk_rst_if slow_clk_rst_if(.clk(clk_slow), .rst_n(rst_slow_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  pwrmgr_if pwrmgr_intf(clk, rst_n, rst_slow_n);

  // dut
  pwrmgr dut (
    .clk_i                (clk       ),
    .rst_ni               (rst_n     ),
    .clk_slow_i           (clk_slow  ),
    .rst_slow_ni          (rst_slow_n),

    .tl_i                 (tl_if.h2d),
    .tl_o                 (tl_if.d2h),

    .pwr_ast_i            (pwrmgr_intf.pwr_ast_rsp),
    .pwr_ast_o            (pwrmgr_intf.pwr_ast_req),

    .pwr_rst_i            (pwrmgr_intf.pwr_rst_rsp),
    .pwr_rst_o            (pwrmgr_intf.pwr_rst_req),

    .pwr_clk_i            (pwrmgr_intf.pwr_clk_rsp),
    .pwr_clk_o            (pwrmgr_intf.pwr_clk_req),

    .pwr_otp_i            (pwrmgr_intf.pwr_otp_rsp),
    .pwr_otp_o            (pwrmgr_intf.pwr_otp_req),

    .pwr_lc_i             (pwrmgr_intf.pwr_lc_rsp ),
    .pwr_lc_o             (pwrmgr_intf.pwr_lc_req ),

    .pwr_flash_i          (pwrmgr_intf.pwr_flash  ),
    .pwr_cpu_i            (pwrmgr_intf.pwr_cpu    ),

    .fetch_en_o           (pwrmgr_intf.fetch_en   ),
    .wakeups_i            (pwrmgr_intf.wakeups    ),
    .rstreqs_i            (pwrmgr_intf.rstreqs    ),

    .strap_o              (pwrmgr_intf.strap      ),
    .low_power_o          (pwrmgr_intf.low_power  ),

    .rom_ctrl_i           (pwrmgr_intf.rom_ctrl   ),

    .esc_rst_tx_i         (pwrmgr_intf.esc_rst_tx ),
    .esc_rst_rx_o         (pwrmgr_intf.esc_rst_rx ),

    .intr_wakeup_o        (pwrmgr_intf.intr_wakeup)
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    slow_clk_rst_if.set_active();

    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "slow_clk_rst_vif", slow_clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
