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

% for clk in clk_freqs.keys():
  wire clk_${clk};
  clk_rst_if ${clk}_clk_rst_if (
    .clk  (clk_${clk}),
    .rst_n()
  );

% endfor

  tl_if tl_if (
    .clk,
    .rst_n(rstmgr_if.resets_o.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  rstmgr_if rstmgr_if (
    .clk_aon,
    .clk,
    .rst_n
  );

  initial begin
    clk_rst_if.set_active();
% for clk in sorted(list(clk_freqs.keys())):
    ${clk}_clk_rst_if.set_active();
% endfor
  end

  `DV_ALERT_IF_CONNECT()

  // dut
  // IMPORTANT: Notice the rst_ni input is connected to one of dut's outputs.
  // This is consistent with rstmgr being the only source of resets.
  rstmgr dut (
    .clk_i        (clk),
    .rst_ni       (rstmgr_if.resets_o.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
% for clk in sorted(list(clk_freqs.keys())):
<% spaces = len("io_div2") - len(clk) %>\
    .clk_${clk}_i${" " * spaces}(clk_${clk}),
% endfor
    .clk_por_i    (clk_io_div4),
    .rst_por_ni   (rstmgr_if.resets_o.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),

    .tl_i      (tl_if.h2d),
    .tl_o      (tl_if.d2h),
    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx),

    .por_n_i(rstmgr_if.por_n),

    .pwr_i(rstmgr_if.pwr_i),
    .pwr_o(rstmgr_if.pwr_o),

    .sw_rst_req_o  (rstmgr_if.sw_rst_req_o),

    .alert_dump_i(rstmgr_if.alert_dump_i),
    .cpu_dump_i  (rstmgr_if.cpu_dump_i),

    .scan_rst_ni(rstmgr_if.scan_rst_ni),
    .scanmode_i (rstmgr_if.scanmode_i),

    .rst_en_o(rstmgr_if.rst_en_o),
    .resets_o(rstmgr_if.resets_o)
  );

  initial begin
    // drive clk and rst_n from clk_rst_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
% for clk in sorted(list(clk_freqs.keys())):
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "${clk}_clk_rst_vif",
                                            ${clk}_clk_rst_if);
% endfor
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);

    uvm_config_db#(virtual pwrmgr_rstmgr_sva_if)::set(null, "*.env", "pwrmgr_rstmgr_sva_vif",
                                                      dut.pwrmgr_rstmgr_sva_if);
    uvm_config_db#(virtual rstmgr_cascading_sva_if)::set(null, "*.env", "rstmgr_cascading_sva_vif",
                                                         dut.rstmgr_cascading_sva_if);
    uvm_config_db#(virtual rstmgr_if)::set(null, "*.env", "rstmgr_vif", rstmgr_if);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  initial begin
    // This may help any code that depends on clk_rst_vif.rst_n in the infrastructure: they won't
    // be able to change but at least the reset value will be true to the environment.
    clk_rst_if.drive_rst_n = 1'b0;
    force clk_rst_if.rst_n = rstmgr_if.resets_o.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel];
  end

endmodule
