// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import clkmgr_env_pkg::*;
  import clkmgr_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;

  // clock outputs
  clkmgr_pkg::clkmgr_ast_out_t clocks_ast_o;
  clkmgr_pkg::clkmgr_out_t clocks_o;

  // clock interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  clk_rst_if main_clk_rst_if(.clk(clk_main), .rst_n(rst_main_n));
  clk_rst_if io_clk_rst_if(.clk(clk_io), .rst_n(rst_io_n));
  clk_rst_if usb_clk_rst_if(.clk(clk_usb), .rst_n(rst_usb_n));
  clk_rst_if aon_clk_rst_if(.clk(clk_aon), .rst_n(rst_aon_n));
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  // Interface to input idle signals.
  clkmgr_idle_if idle_if(.clk(clk));

  // Interface to pwrmgr input.
  clkmgr_pwrmgr_if pwrmgr_if(.clk(clk));

  initial begin
    // Clocks must be set to active at time 0. The rest of the clock configuration happens
    // in clkmgr_base_vseq.sv.
    main_clk_rst_if.set_active();
    io_clk_rst_if.set_active();
    usb_clk_rst_if.set_active();
    aon_clk_rst_if.set_active();
  end

  pwrmgr_pkg::pwr_clk_req_t pwr_i;
  always_comb pwr_i.ip_clk_en = pwrmgr_if.ip_clk_en;

  pwrmgr_pkg::pwr_clk_rsp_t pwr_o;
  always_comb pwrmgr_if.clk_status = pwr_o.clk_status;

  // dut
  clkmgr dut (
    .clk_i                (clk       ),
    .rst_ni               (rst_n     ),

    .clk_main_i           (main_clk_rst_if.clk   ),
    .rst_main_ni          (main_clk_rst_if.rst_n ),
    .clk_io_i             (io_clk_rst_if.clk     ),
    .rst_io_ni            (io_clk_rst_if.rst_n   ),
    .clk_usb_i            (usb_clk_rst_if.clk    ),
    .rst_usb_ni           (usb_clk_rst_if.rst_n  ),
    .clk_aon_i            (usb_clk_rst_if.clk    ),

    .rst_io_div2_ni       (usb_clk_rst_if.rst_n  ),
    // Setting as above...
    .rst_io_div4_ni       (usb_clk_rst_if.rst_n  ),

    .tl_i                 (tl_if.h2d ),
    .tl_o                 (tl_if.d2h ),

    .pwr_i                (pwr_i     ),
    .pwr_o                (pwr_o     ),

    .scanmode_i           (lc_ctrl_pkg::Off     ),
    .idle_i               (idle_if.idle),

    .ast_clk_byp_req_o    ( /* FIXME: connect this */ ),
    .ast_clk_byp_ack_i    (lc_ctrl_pkg::On      ),
    .lc_clk_byp_req_i     (lc_ctrl_pkg::Off     ),
    .lc_clk_byp_ack_o     ( /* FIXME: connect this */ ),

    .jitter_en_o          ( /* FIXME: connect this */ ),
    .clocks_ast_o         (clocks_ast_o ),
    .clocks_o             (clocks_o     )

    // Hook alert and interrupt pins when added.
    // .alert_rx_i          (alert_rx ),
    // .alert_tx_o          (alert_tx )
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "main_clk_rst_vif", main_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "io_clk_rst_vif", io_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "usb_clk_rst_vif", usb_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "aon_clk_rst_vif", aon_clk_rst_if);

    uvm_config_db#(virtual clkmgr_idle_if)::set(null, "*.env", "clkmgr_idle_vif", idle_if);
    uvm_config_db#(virtual clkmgr_pwrmgr_if)::set(null, "*.env", "clkmgr_pwrmgr_vif", pwrmgr_if);

    // FIXME Un-comment this once interrupts are created for this ip.
//    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);

    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
