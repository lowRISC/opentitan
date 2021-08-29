// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import rstmgr_env_pkg::*;
  import rstmgr_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire clk_aon;
  wire clk_io_div4_i;
  wire clk_main_i;
  wire clk_io_i;
  wire clk_io_div2_i;
  wire clk_usb_i;

  wire devmode;

  // interfaces
  clk_rst_if clk_rst_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  clk_rst_if aon_clk_rst_if (.clk(clk_aon));
  clk_rst_if io_clk_rst_if (.clk(clk_io));
  clk_rst_if io_div2_clk_rst_if (.clk(clk_io_div2));
  clk_rst_if io_div4_clk_rst_if (.clk(clk_io_div4));
  clk_rst_if main_clk_rst_if (.clk(clk_main));
  clk_rst_if usb_clk_rst_if (.clk(clk_usb));

  pins_if #(1) devmode_if (devmode);
  tl_if tl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );

  rstmgr_if rstmgr_if (
    .clk  (clk),
    .rst_n(rst_n)
  );

  initial begin
    clk_rst_if.set_active();
    aon_clk_rst_if.set_active();
    io_clk_rst_if.set_active();
    io_div2_clk_rst_if.set_active();
    io_div4_clk_rst_if.set_active();
    main_clk_rst_if.set_active();
    usb_clk_rst_if.set_active();
  end

  `DV_ALERT_IF_CONNECT

  // dut
  // IMPORTANT: Notice the rst_ni input is connected to one of dut's outputs.
  // This is consistent with rstmgr being the only source of resets.
  rstmgr dut (
    .clk_i        (clk),
    .rst_ni       (rstmgr_if.resets_o.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .clk_aon_i    (clk_aon),
    .clk_io_div4_i(clk_io_div4),
    .clk_main_i   (clk_main),
    .clk_io_i     (clk_io),
    .clk_io_div2_i(clk_io_div2),
    .clk_usb_i    (clk_usb),

    .tl_i      (tl_if.h2d),
    .tl_o      (tl_if.d2h),
    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx),

    .por_n_i(rstmgr_if.por_n),

    .pwr_i(rstmgr_if.pwr_i),
    .pwr_o(rstmgr_if.pwr_o),

    .rst_cpu_n_i(rstmgr_if.cpu_i.rst_cpu_n),
    .ndmreset_req_i(rstmgr_if.cpu_i.ndmreset_req),

    .alert_dump_i(rstmgr_if.alert_dump_i),

    .cpu_dump_i(rstmgr_if.cpu_dump_i),

    .scan_rst_ni(rstmgr_if.scan_rst_ni),
    .scanmode_i (rstmgr_if.scanmode_i),

    .resets_ast_o(rstmgr_if.resets_ast_o),
    .resets_o    (rstmgr_if.resets_o)
  );

  initial begin
    // drive clk and rst_n from clk_rst_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "aon_clk_rst_vif", aon_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "io_clk_rst_vif", io_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "io_div2_clk_rst_vif",
                                            io_div2_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "io_div4_clk_rst_vif",
                                            io_div4_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "main_clk_rst_vif", main_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "usb_clk_rst_vif", usb_clk_rst_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);

    uvm_config_db#(virtual pwrmgr_rstmgr_sva_if)::set(null, "*.env", "pwrmgr_rstmgr_sva_vif",
                                                      dut.pwrmgr_rstmgr_sva_if);
    uvm_config_db#(virtual rstmgr_if)::set(null, "*.env", "rstmgr_vif", rstmgr_if);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
