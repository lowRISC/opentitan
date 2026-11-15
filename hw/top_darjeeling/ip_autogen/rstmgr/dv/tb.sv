// Copyright lowRISC contributors (OpenTitan project).
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
  clk_rst_if clk_rst_if (
    .clk,
    .rst_n
  );

  wire clk_aon;
  clk_rst_if aon_clk_rst_if (
    .clk  (clk_aon),
    .rst_n()
  );

  wire clk_io;
  clk_rst_if io_clk_rst_if (
    .clk  (clk_io),
    .rst_n()
  );

  wire clk_main;
  clk_rst_if main_clk_rst_if (
    .clk  (clk_main),
    .rst_n()
  );


  tl_if tl_if (
    .clk,
    .rst_n(rstmgr_if.resets_o.rst_lc_io_n[rstmgr_pkg::DomainMainSel])
  );

  rstmgr_if rstmgr_if (
    .clk_aon,
    .clk,
    .rst_n
  );

  initial begin
    clk_rst_if.set_active();
    aon_clk_rst_if.set_active();
    io_clk_rst_if.set_active();
    main_clk_rst_if.set_active();
  end

  `DV_ALERT_IF_CONNECT()

  // The DUT is the two partitions of the reset manager, connected the same as a top connects them
  // when both are in the same power domain.
  // rst_ni and rst_por_ni come from outputs of the reset manager itself, because the reset manager
  // is the only source of resets.
  rstmgr_pkg::intraip_s2p_t intraip_s2p;
  rstmgr_pkg::intraip_p2s_t intraip_p2s;
  rstmgr_pkg::rstmgr_out_primary_t resets_primary;
  rstmgr_pkg::rstmgr_out_secondary_t resets_secondary;

  rstmgr_part_primary dut_primary (
    .clk_i        (clk),
    .rst_ni       (rstmgr_if.resets_o.rst_lc_io_n[rstmgr_pkg::DomainMainSel]),
    .clk_aon_i    (clk_aon),
    .clk_io_i     (clk_io),
    .clk_main_i   (clk_main),
    .clk_por_i    (clk_io),
    .rst_por_ni   (rstmgr_if.resets_o.rst_por_io_n[rstmgr_pkg::DomainMainSel]),

    .tl_i      (tl_if.h2d),
    .tl_o      (tl_if.d2h),
    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx),

    .sw_rst_req_o  (rstmgr_if.sw_rst_req_o),

    .alert_dump_i(rstmgr_if.alert_dump_i),
    .cpu_dump_i  (rstmgr_if.cpu_dump_i),

    .rst_en_o(),
    .resets_o(resets_primary),

    .intraip_s2p_i(intraip_s2p),
    .intraip_p2s_o(intraip_p2s)
  );

  rstmgr_part_secondary dut_secondary (
    .rst_ni       (rstmgr_if.resets_o.rst_lc_io_n[rstmgr_pkg::DomainAonSel]),
    .clk_aon_i    (clk_aon),
    .rst_por_ni   (rstmgr_if.resets_o.rst_por_io_n[rstmgr_pkg::DomainAonSel]),

    .por_n_i(rstmgr_if.por_n),

    .pwr_i(rstmgr_if.pwr_i),
    .pwr_o(rstmgr_if.pwr_o),

    .scan_rst_ni(rstmgr_if.scan_rst_ni),
    .scanmode_i (rstmgr_if.scanmode_i),

    .resets_secondary_o(resets_secondary),

    .intraip_s2p_o(intraip_s2p),
    .intraip_p2s_i(intraip_p2s)
  );

  // rstmgr_if presents the resets of both partitions as one struct.
  assign rstmgr_if.resets_primary = resets_primary;
  assign rstmgr_if.resets_secondary = resets_secondary;

  initial begin
    // drive clk and rst_n from clk_rst_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "aon_clk_rst_vif",
                                            aon_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "io_clk_rst_vif",
                                            io_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "main_clk_rst_vif",
                                            main_clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);

    uvm_config_db#(virtual pwrmgr_rstmgr_sva_if)::set(null, "*.env", "pwrmgr_rstmgr_sva_vif",
                                                      dut_secondary.pwrmgr_rstmgr_sva_if);
    uvm_config_db#(virtual rstmgr_cascading_primary_sva_if)::set(
        null, "*.env", "rstmgr_cascading_primary_sva_vif",
        dut_primary.rstmgr_cascading_primary_sva_if);
    uvm_config_db#(virtual rstmgr_cascading_secondary_sva_if)::set(
        null, "*.env", "rstmgr_cascading_secondary_sva_vif",
        dut_secondary.rstmgr_cascading_secondary_sva_if);
    uvm_config_db#(virtual rstmgr_if)::set(null, "*.env", "rstmgr_vif", rstmgr_if);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  initial begin
    // This may help any code that depends on clk_rst_vif.rst_n in the infrastructure: they won't
    // be able to change but at least the reset value will be true to the environment.
    clk_rst_if.drive_rst_n = 1'b0;
    force clk_rst_if.rst_n = rstmgr_if.resets_o.rst_lc_io_n[rstmgr_pkg::DomainMainSel];
  end

endmodule
