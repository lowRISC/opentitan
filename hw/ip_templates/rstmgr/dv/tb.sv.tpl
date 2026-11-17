// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
<% 
all_clks = set(clk_freqs.keys())

if "io_div4" in all_clks:
    preferred_domain = "io_div4"
elif "io" in all_clks:
    preferred_domain = "io"
else:
    assert 0, "No preferred clock available"

preferred_rst_n = f"rst_lc_{preferred_domain}_n"
preferred_por_n = f"rst_por_{preferred_domain}_n"
%>\
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
    .rst_n(rstmgr_if.resets_o.${preferred_rst_n}[rstmgr_pkg::DomainMainSel])
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

<%
from ipgen.manager_split import rstmgr_clocks
tb_split_clks = rstmgr_clocks(clk_freqs, leaf_rsts, rst_ni)
%>\
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
    .rst_ni       (rstmgr_if.resets_o.${preferred_rst_n}[rstmgr_pkg::DomainMainSel]),
% for clk in tb_split_clks.ports['primary']:
<% port = f".clk_{clk}_i" %>\
    ${port.ljust(14)}(clk_${clk}),
% endfor
    .clk_por_i    (clk_${preferred_domain}),
    .rst_por_ni   (rstmgr_if.resets_o.${preferred_por_n}[rstmgr_pkg::DomainMainSel]),

    .tl_i      (tl_if.h2d),
    .tl_o      (tl_if.d2h),
    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx),

    .sw_rst_req_o  (rstmgr_if.sw_rst_req_o),

    .alert_dump_i(rstmgr_if.alert_dump_i),
    .cpu_dump_i  (rstmgr_if.cpu_dump_i),

% for intf in export_rsts:
    .resets_${intf}_o(),
% endfor
    .rst_en_o(),
    .resets_o(resets_primary),

    .intraip_s2p_i(intraip_s2p),
    .intraip_p2s_o(intraip_p2s)
  );

  rstmgr_part_secondary dut_secondary (
    .rst_ni       (rstmgr_if.resets_o.${preferred_rst_n}[rstmgr_pkg::DomainAonSel]),
% for clk in tb_split_clks.ports['secondary']:
<% port = f".clk_{clk}_i" %>\
    ${port.ljust(14)}(clk_${clk}),
% endfor
    .rst_por_ni   (rstmgr_if.resets_o.${preferred_por_n}[rstmgr_pkg::DomainAonSel]),

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
% for clk in sorted(list(clk_freqs.keys())):
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "${clk}_clk_rst_vif",
                                            ${clk}_clk_rst_if);
% endfor
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
    force clk_rst_if.rst_n = rstmgr_if.resets_o.${preferred_rst_n}[rstmgr_pkg::DomainMainSel];
  end

endmodule
