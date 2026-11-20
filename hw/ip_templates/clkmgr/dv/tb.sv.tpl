// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
<%
all_src_names = sorted(s['name'] for s in src_clks.values())
all_derived_names = sorted(s['name'] for s in derived_clks.values())
rg_srcs = list(sorted({sig['src_name'] for sig
                       in typed_clocks['rg_clks'].values()}))
%>\
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import clkmgr_env_pkg::*;
  import clkmgr_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // clock interfaces
  wire clk, rst_n, rst_shadowed_n;
  clk_rst_if clk_rst_if (
    .clk  (clk),
    .rst_n(rst_n)
  );

% for src_name in all_src_names:
  wire clk_${src_name}, rst_${src_name}_n;
  clk_rst_if ${src_name}_clk_rst_if (
    .clk  (clk_${src_name}),
    .rst_n(rst_${src_name}_n)
  );

% endfor
% for src_name in all_derived_names:
  wire rst_${src_name}_n;
  clk_rst_if ${src_name}_clk_rst_if (
    .clk  (),
    .rst_n(rst_${src_name}_n)
  );
% endfor
% for clk_family in parent_child_clks.values():
  % for src in clk_family:
  clk_rst_if root_${src}_clk_rst_if (
    .clk  (),
    .rst_n(rst_root_${src}_n)
  );
  % endfor
% endfor
  tl_if tl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );

  // The clkmgr interface.
  clkmgr_if clkmgr_if (
    .clk(clk),
    .rst_n(rst_n),
% for src_name in all_src_names:
<% sep = "" if loop.last else "," %>\
    .rst_${src_name}_n(rst_${src_name}_ni)${sep}
% endfor
  );

  // The registers are in the primary partition of the clkmgr.
  bind clkmgr_part_primary clkmgr_csrs_if clkmgr_csrs_if (
    .clk(clk_i),
    .recov_err_csr({
% for src in sorted(rg_srcs, reverse=True):
        u_reg.u_recov_err_code_${src}_timeout_err.qs,
% endfor
% for src in sorted(rg_srcs, reverse=True):
        u_reg.u_recov_err_code_${src}_measure_err.qs,
% endfor
        u_reg.u_recov_err_code_shadow_update_err.qs
    }),
    .fatal_err_csr({
        u_reg.u_fatal_err_code_shadow_storage_err.qs,
        u_reg.u_fatal_err_code_idle_cnt.qs,
        u_reg.u_fatal_err_code_reg_intg.qs
     }),
    .clk_enables({
% for clk_name in list(reversed(typed_clocks['sw_clks'])):
<% sep = "})," if loop.last else "," %>\
  % if len(typed_clocks['sw_clks']) == 1:
        reg2hw.clk_enables.q${sep}
  % else:
        reg2hw.clk_enables.${clk_name}_en.q${sep}
  % endif
% endfor
    .clk_hints({
        reg2hw.clk_hints.clk_main_otbn_hint.q,
        reg2hw.clk_hints.clk_main_kmac_hint.q,
        reg2hw.clk_hints.clk_main_hmac_hint.q,
        reg2hw.clk_hints.clk_main_aes_hint.q})
  );

  rst_shadowed_if rst_shadowed_if (
    .rst_n(rst_n),
    .rst_shadowed_n(rst_shadowed_n)
  );

  initial begin
    // Clocks must be set to active at time 0. The rest of the clock configuration happens
    // in clkmgr_base_vseq.sv.
    clk_rst_if.set_active();
% for src_name in all_src_names:
    ${src_name}_clk_rst_if.set_active();
% endfor
% for src_name in all_derived_names:
    ${src_name}_clk_rst_if.set_active();
% endfor
% for clk_family in parent_child_clks.values():
  % for src in clk_family:
    root_${src}_clk_rst_if.set_active();
  % endfor
% endfor
  end

  `DV_ALERT_IF_CONNECT()

<%
from ipgen.manager_split import clkmgr_split_srcs
tb_primary_srcs, tb_secondary_srcs = clkmgr_split_srcs(src_clks)
%>\
  // The DUT is the two partitions of the clock manager, connected the same as a top connects them
  // when both are in the same power domain.
  clkmgr_pkg::intraip_s2p_t intraip_s2p;
  clkmgr_pkg::intraip_p2s_t intraip_p2s;
  clkmgr_pkg::clkmgr_out_primary_t clocks_primary;
  clkmgr_pkg::clkmgr_out_secondary_t clocks_secondary;

  clkmgr_part_primary dut_primary (
    .clk_i(clk),
    .rst_ni(rst_n),
    .rst_shadowed_ni(rst_shadowed_n),

% for src in tb_primary_srcs:
    .clk_${src['name']}_i (clk_${src['name']}),
% endfor
% for src_name in all_src_names:
    .rst_${src_name}_ni(rst_${src_name}_n),
% endfor
% for src_name in all_derived_names:
    .rst_${src_name}_ni(rst_${src_name}_n),
% endfor
    // ICEBOX(#17934): differentiate the root resets as mentioned for rst_io_ni above.
    .rst_root_ni(rst_root_io_n),
% for clk_family in parent_child_clks.values():
  % for src in clk_family:
    .rst_root_${src}_ni(rst_root_${src}_n),
  % endfor
% endfor

    .tl_i(tl_if.h2d),
    .tl_o(tl_if.d2h),

    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx),

    .idle_i    (clkmgr_if.idle_i),

% if ext_clk_bypass:
    .lc_hw_debug_en_i(clkmgr_if.lc_hw_debug_en_i),
    .all_clk_byp_req_o(clkmgr_if.all_clk_byp_req),
    .all_clk_byp_ack_i(clkmgr_if.all_clk_byp_ack),
    .io_clk_byp_req_o(clkmgr_if.io_clk_byp_req),
    .io_clk_byp_ack_i(clkmgr_if.io_clk_byp_ack),
    .lc_clk_byp_req_i(clkmgr_if.lc_clk_byp_req),
    .lc_clk_byp_ack_o(clkmgr_if.lc_clk_byp_ack),
    .div_step_down_req_i(clkmgr_if.div_step_down_req),
    .hi_speed_sel_o(clkmgr_if.hi_speed_sel),
    .calib_rdy_i(clkmgr_if.calib_rdy),

% endif
    .cg_en_o(),

    .jitter_en_o(clkmgr_if.jitter_en_o),
% for intf in exported_clks:
    .clocks_${intf}_o(),
% endfor
    .clocks_o   (clocks_primary),

    .intraip_s2p_i(intraip_s2p),
    .intraip_p2s_o(intraip_p2s)
  );

  clkmgr_part_secondary dut_secondary (
% for src in tb_secondary_srcs:
    .clk_${src['name']}_i (clk_${src['name']}),
    .rst_${src['name']}_ni(rst_${src['name']}_n),
% endfor

    .pwr_i(clkmgr_if.pwr_i),
    .pwr_o(clkmgr_if.pwr_o),
    .main_pd_aon_clk_en_i(clkmgr_if.main_pd_aon_clk_en),

    .scanmode_i(clkmgr_if.scanmode_i),

    .clocks_secondary_o(clocks_secondary),

    .intraip_s2p_o(intraip_s2p),
    .intraip_p2s_i(intraip_p2s)
  );

  // clkmgr_if presents the clocks of both partitions as one struct.
  assign clkmgr_if.clocks_primary = clocks_primary;
  assign clkmgr_if.clocks_secondary = clocks_secondary;

  initial begin
    // Register interfaces with uvm.
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
% for src_name in all_src_names:
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "${src_name}_clk_rst_vif", ${src_name}_clk_rst_if);
% endfor
% for src_name in all_derived_names:
    % if len(src_name) > len("main"):
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "${src_name}_clk_rst_vif",
                                            ${src_name}_clk_rst_if);
    % else:
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "${src_name}_clk_rst_vif", ${src_name}_clk_rst_if);
    % endif
% endfor
% for clk_family in parent_child_clks.values():
  % for src in clk_family:
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "root_${src}_clk_rst_vif",
                                            root_${src}_clk_rst_if);
  % endfor
% endfor
    uvm_config_db#(virtual clkmgr_if)::set(null, "*.env", "clkmgr_vif", clkmgr_if);

    uvm_config_db#(virtual clkmgr_csrs_if)::set(null, "*.env", "clkmgr_csrs_vif",
                                                dut_primary.clkmgr_csrs_if);

    // FIXME Un-comment this once interrupts are created for this ip.
    // uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);

    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif",
                                                 rst_shadowed_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
