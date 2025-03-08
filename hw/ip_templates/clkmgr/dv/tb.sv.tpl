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

  bind clkmgr clkmgr_csrs_if clkmgr_csrs_if (
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
% for clk in [c for c in reversed(typed_clocks['sw_clks'].values())]:
<% sep = "})," if loop.last else "," %>\
        reg2hw.clk_enables.clk_${clk['src_name']}_peri_en.q${sep}
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

  // dut
  clkmgr dut (
    .clk_i(clk),
    .rst_ni(rst_n),
    .rst_shadowed_ni(rst_shadowed_n),

% for src_name in all_src_names:
    .clk_${src_name}_i (clk_${src_name}),
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

    .pwr_i(clkmgr_if.pwr_i),
    .pwr_o(clkmgr_if.pwr_o),

    .scanmode_i(clkmgr_if.scanmode_i),
    .idle_i    (clkmgr_if.idle_i),

    .lc_hw_debug_en_i(clkmgr_if.lc_hw_debug_en_i),
    .all_clk_byp_req_o(clkmgr_if.all_clk_byp_req),
    .all_clk_byp_ack_i(clkmgr_if.all_clk_byp_ack),
    .io_clk_byp_req_o(clkmgr_if.io_clk_byp_req),
    .io_clk_byp_ack_i(clkmgr_if.io_clk_byp_ack),
    .lc_clk_byp_req_i(clkmgr_if.lc_clk_byp_req),
    .lc_clk_byp_ack_o(clkmgr_if.lc_clk_byp_ack),
    .div_step_down_req_i(clkmgr_if.div_step_down_req),

    .cg_en_o(),

    .jitter_en_o(clkmgr_if.jitter_en_o),
    .clocks_o   (clkmgr_if.clocks_o),

    .calib_rdy_i(clkmgr_if.calib_rdy),
    .hi_speed_sel_o(clkmgr_if.hi_speed_sel)
  );

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
                                                dut.clkmgr_csrs_if);

    // FIXME Un-comment this once interrupts are created for this ip.
    // uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);

    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif",
                                                 rst_shadowed_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
