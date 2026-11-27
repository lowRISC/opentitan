// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Primary partition of the split reset manager.
//
// The primary partition hosts:
//  - the register file and the alerts. RESET_REQ, RESET_INFO, ALERT_REGWEN, ALERT_INFO_CTRL,
//    CPU_REGWEN, CPU_INFO_CTRL and ERR_CODE are external, and the secondary partition keeps their
//    state.
//  - the storage of the crash dumps (ALERT_INFO and CPU_INFO). The secondary partition decides
//    the captures.
//  - the leaf resets that the secondary partition does not host.

`include "prim_assert.sv"

<%
from topgen.lib import Name
from ipgen.manager_split import (rstmgr_clocks, rstmgr_hosted_domains, rstmgr_is_array,
                                 rstmgr_out_domains, rstmgr_routed_roots)
split_clks = rstmgr_clocks(clk_freqs, leaf_rsts, rst_ni, aon_clock)
# The clocks that this partition uses, the ones that it receives (ports), and the ones that it
# forwards to the secondary partition.
primary_port_clk_names = split_clks.ports['primary']
secondary_fwd_clk_names = split_clks.forwarded['secondary']
# One error flag per leaf instance that this partition hosts (a shadowed leaf has two instances).
n_err = sum((2 if r['shadowed'] else 1) *
            len(rstmgr_hosted_domains(r, 'primary'))
            for r in leaf_rsts)
PART = 'primary'
OUT = 'resets_o'
# Each leaf reset drives its output field directly, in the shape of the output struct, or a local
# net if this partition does not output it (it only crosses to the other partition). Its reset
# asserted indication goes straight to where it leaves this partition.
def leaf_dst(rst, n, d):
    out_doms = rstmgr_out_domains(rst, PART, n)
    if d in out_doms:
        sel = f"[Domain{d}Sel]" if rstmgr_is_array(out_doms, power_domains) else ""
        return f"{OUT}.rst_{n}_n{sel}"
    return f"rst_{n}_n_{d.lower()}_local"
def en_dst(rst, n, d):
    if PART == 'primary':
        sel = f"[Domain{d}Sel]" if rstmgr_is_array(rst['domains'], power_domains) else ""
        return f"rst_en_o.{n}{sel}"
    return f"intraip_s2p_o.rst_en_{n}_{d.lower()}"
def local_leaves(rsts):
    out = []
    for r in rsts:
        names = [r['name']] + ([r['name'] + '_shadowed'] if r['shadowed'] else [])
        for n in names:
            for d in rstmgr_hosted_domains(r, PART):
                if d not in rstmgr_out_domains(r, PART, n):
                    out.append(f"rst_{n}_n_{d.lower()}_local")
    return out
%>\

module rstmgr_part_primary
  import rstmgr_pkg::*;
  import rstmgr_reg_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  // Number of cycles a differential skew is tolerated on the alert signal
  parameter int unsigned AlertSkewCycles = 1,
  parameter bit SecCheck = 1,
  parameter int SecMaxSyncDelay = 2
) (
  // Primary module clocks
  input clk_i,
  input rst_ni,
% for clk in primary_port_clk_names:
  input clk_${clk}_i,
% endfor
  // These ports are the POR clock and the POR reset. The crash dump and its sync registers use
  // them, so that the capture and its enable use the same clock, and an escalation's reset does not
  // clear them. Every clock except the always-on clock enters here. Thus the secondary partition
  // also gets the POR clock from here, for its reset controllers and RESET_INFO.
  input clk_por_i,
  input rst_por_ni,

  // Bus Interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Interface to alert handler
  input alert_handler_pkg::alert_crashdump_t alert_dump_i,

  // Interface to cpu crash dump
  input rv_core_ibex_pkg::cpu_crash_dump_t cpu_dump_i,

  // Reset asserted indications going to alert handler
  output rstmgr_rst_en_primary_t rst_en_o,

  // reset outputs
% for intf in export_rsts:
  output rstmgr_${intf}_out_t resets_${intf}_o,
% endfor
  output rstmgr_out_primary_t resets_o,

  // inter-partition signalling
  input intraip_s2p_t intraip_s2p_i,
  output intraip_p2s_t intraip_p2s_o
);

  // The scan signals enter only the secondary partition. This partition takes them from
  // intraip_s2p_i. The scan reset gets a net of its own, the same as the roots, so that the
  // crossing struct carries only data where this partition uses it directly.
  logic scan_rst_n;
  assign scan_rst_n = intraip_s2p_i.scan_rst_n;

  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  // The crash dump and its registers use the POR clock and the POR reset. Thus an escalation's
  // reset does not clear the crash dump, and software can read it after the escalation. This POR is
  // the POR of the power domain that powers down, so a deep sleep resets them.
  logic clk_por;
  logic rst_por_n;
  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_por_clk_buf (
    .clk_i(clk_por_i),
    .clk_o(clk_por)
  );

  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_por_rst_buf (
    .clk_i(rst_por_ni),
    .clk_o(rst_por_n)
  );

% if local_leaves(output_rsts):
  // The leaf resets that this partition generates but does not output. They only cross to the
  // secondary partition.
  % for net in local_leaves(output_rsts):
  logic ${net};
  % endfor
% endif

  ////////////////////////////////////////////////////
  // Register Interface                             //
  ////////////////////////////////////////////////////

  rstmgr_reg_pkg::rstmgr_reg2hw_t reg2hw;
  rstmgr_reg_pkg::rstmgr_hw2reg_t hw2reg;

  logic reg_intg_err;
  // SEC_CM: BUS.INTEGRITY
  // SEC_CM: SW_RST.CONFIG.REGWEN, DUMP_CTRL.CONFIG.REGWEN
  rstmgr_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(reg_intg_err)
  );


  ////////////////////////////////////////////////////
  // Errors                                         //
  ////////////////////////////////////////////////////

  // consistency check errors
% if n_err:
  logic [${n_err-1}:0] cnsty_chk_errs;
  logic [${n_err-1}:0] fsm_errs;
% endif

  // ERR_CODE is external, so the register file keeps no state for it. The errors of this partition
  // go to the secondary partition, which keeps the record of all of them in the always-on power
  // domain. ERR_CODE and the alerts read that record.
  assign intraip_p2s_o.reg_intg_err  = reg_intg_err;
  // The clocks that the secondary partition uses, which enter this partition only.
<% fwd_clks = ['clk', 'clk_por'] + [f'clk_{c}' for c in secondary_fwd_clk_names] %>\
<% fwd_w = max(len(c) for c in fwd_clks) %>\
% for c in fwd_clks:
  assign intraip_p2s_o.${c.ljust(fwd_w)} = ${c}_i;
% endfor
  assign intraip_p2s_o.cnsty_chk_err = ${"|cnsty_chk_errs" if n_err else "1'b0"};
  assign intraip_p2s_o.fsm_err       = ${"|fsm_errs" if n_err else "1'b0"};

  assign hw2reg.err_code.reg_intg_err.d          = intraip_s2p_i.reg_intg_err_q;
  assign hw2reg.err_code.reset_consistency_err.d = intraip_s2p_i.cnsty_chk_err_q;
  assign hw2reg.err_code.fsm_err.d               = intraip_s2p_i.fsm_err_q;
  ////////////////////////////////////////////////////
  // Alerts                                         //
  ////////////////////////////////////////////////////
  logic [NumAlerts-1:0] alert_test, alerts;

  // All of these are fatal alerts
  assign alerts[0] = intraip_s2p_i.reg_intg_err_q | intraip_s2p_i.fsm_err_q;

  assign alerts[1] = intraip_s2p_i.cnsty_chk_err_q;

  assign alert_test = {
    reg2hw.alert_test.fatal_cnsty_fault.q & reg2hw.alert_test.fatal_cnsty_fault.qe,
    reg2hw.alert_test.fatal_fault.q & reg2hw.alert_test.fatal_fault.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .SkewCycles(AlertSkewCycles),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[i]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  ////////////////////////////////////////////////////
  // Source resets in the system                    //
  ////////////////////////////////////////////////////

  // The secondary partition generates the root resets, which are the POR root and the lc and sys
  // sources of each power domain. This partition receives the roots that its leaves use, in
  // intraip_s2p_i.
% for root, domain in rstmgr_routed_roots(leaf_rsts):
  //  - rst_${root}_n_${domain.lower()}
% endfor


  ////////////////////////////////////////////////////
  // leaf reset in the system                       //
  // These should all be generated                  //
  ////////////////////////////////////////////////////
  // Each leaf generates only the variants that this partition hosts. Nothing is tied off.

<% err_idx = 0 %>\
  // The roots that the leaves here have as parents come from the secondary partition. Each root
  // gets a local net, so a leaf connects to a plain signal rather than to a field of intraip_s2p_i.
  // A force on the parent reset of a leaf in the DV then reaches an ordinary net.
% for root, domain in rstmgr_routed_roots(leaf_rsts):
  logic rst_${root}_n_${domain.lower()};
  assign rst_${root}_n_${domain.lower()} = intraip_s2p_i.rst_${root}_n_${domain.lower()};
% endfor

% for rst in leaf_rsts:
<%
names = [rst['name']]
if rst['shadowed']:
  names.append(f"{rst['name']}_shadowed")
hosted = rstmgr_hosted_domains(rst, 'primary')
arr = bool(hosted) and rstmgr_is_array(hosted, power_domains)
leaf_clk = f"clk_{rst['clock']}_i"
%>\
  % if hosted:
  // Generating resets for ${names[0]}
  // Power Domains: ${rst['domains']}, hosted in this partition: ${hosted}
  // Shadowed: ${rst['shadowed']}
    % for name in names:
<% rst_name_camel = Name.to_camel_case(name) %>\
      % for domain in hosted:
<% sel = f"[Domain{domain}Sel]" if arr else "" %>\
  rstmgr_leaf_rst #(
        % if names[0]==rst_ni:
    .SecCheck(0),
        % else:
    .SecCheck(SecCheck),
        % endif
    .SecMaxSyncDelay(SecMaxSyncDelay),
        % if rst['sw']:
    .SwRstReq(1'b1)
        % else:
    .SwRstReq(1'b0)
        % endif
  ) u_d${domain.lower()}_${name} (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(${leaf_clk}),
    .parent_rst_ni(rst_${rst['parent']}_n_${domain.lower()}),
        % if rst['sw']:
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[${name.upper()}].q),
        % else:
    .sw_rst_req_ni(1'b1),
        % endif
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(${en_dst(rst, name, domain)}),
    .leaf_rst_o(${leaf_dst(rst, name, domain)}),
    .err_o(cnsty_chk_errs[${err_idx}]),
    .fsm_err_o(fsm_errs[${err_idx}])
  );
<% err_idx += 1 %>\
        % if names[0]!=rst_ni:
  if (SecCheck) begin : gen_d${domain.lower()}_${name}_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    D${domain.capitalize()}${rst_name_camel}FsmCheck_A,
    u_d${domain.lower()}_${name}.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
        % endif
      % endfor
    % endfor
  % endif
% endfor

  ////////////////////////////////////////////////////
  // Reset info construction                        //
  ////////////////////////////////////////////////////

  // RESET_REQ is external (hwext). The secondary partition keeps the software reset request in
  // the always-on power domain, and sends it to the power manager. This partition reads it, and
  // forwards the software writes.
  assign hw2reg.reset_req.d         = intraip_s2p_i.reset_req_q;
  assign intraip_p2s_o.reset_req_we = reg2hw.reset_req.qe;
  assign intraip_p2s_o.reset_req_wd = prim_mubi_pkg::mubi4_t'(reg2hw.reset_req.q);

  // RESET_INFO is external (hwext). The secondary partition keeps the reset reasons in the
  // always-on power domain, so that they survive a deep sleep. This partition reads them. It
  // decodes the software writes into one clear per bit (rw1c), and forwards them.
  assign hw2reg.reset_info = intraip_s2p_i.reset_info_q;
  assign intraip_p2s_o.por_clr =
      reg2hw.reset_info.por.qe & reg2hw.reset_info.por.q;
  assign intraip_p2s_o.low_power_exit_clr =
      reg2hw.reset_info.low_power_exit.qe & reg2hw.reset_info.low_power_exit.q;
  assign intraip_p2s_o.sw_reset_clr =
      reg2hw.reset_info.sw_reset.qe & reg2hw.reset_info.sw_reset.q;
  assign intraip_p2s_o.hw_req_clr =
      {rstmgr_reg_pkg::NumHwResets{reg2hw.reset_info.hw_req.qe}} & reg2hw.reset_info.hw_req.q;

  ////////////////////////////////////////////////////
  // Crash info capture                             //
  ////////////////////////////////////////////////////

  // The secondary partition decides the captures: a hardware reset or a low power entry while a
  // dump is enabled. It keeps the dump controls in the always-on power domain, and a hardware reset
  // clears their EN fields, so that no more information is captured until software enables the
  // dump again. This partition stores the dumps.

  // ALERT_REGWEN, ALERT_INFO_CTRL, CPU_REGWEN and CPU_INFO_CTRL are external (hwext). The secondary
  // partition keeps them, and this partition reads them. It forwards a write of 0 to a lock, which
  // clears it (rw0c), decodes the writes to an EN field into a set and a clear, and forwards the
  // writes to an INDEX field. The register file blocks the writes to a control while its lock is
  // clear.

  // ALERT_REGWEN and ALERT_INFO_CTRL.
  assign hw2reg.alert_regwen.d          = intraip_s2p_i.alert_regwen_q;
  assign intraip_p2s_o.alert_regwen_clr = reg2hw.alert_regwen.qe & ~reg2hw.alert_regwen.q;

  assign hw2reg.alert_info_ctrl.en.d    = intraip_s2p_i.alert_info_en_q;
  assign hw2reg.alert_info_ctrl.index.d = intraip_s2p_i.alert_info_idx_q;
  assign intraip_p2s_o.alert_info_en_set =
      reg2hw.alert_info_ctrl.en.qe & reg2hw.alert_info_ctrl.en.q;
  assign intraip_p2s_o.alert_info_en_clr =
      reg2hw.alert_info_ctrl.en.qe & ~reg2hw.alert_info_ctrl.en.q;
  assign intraip_p2s_o.alert_info_idx_we = reg2hw.alert_info_ctrl.index.qe;
  assign intraip_p2s_o.alert_info_idx_wd = reg2hw.alert_info_ctrl.index.q;

  // CPU_REGWEN and CPU_INFO_CTRL.
  assign hw2reg.cpu_regwen.d          = intraip_s2p_i.cpu_regwen_q;
  assign intraip_p2s_o.cpu_regwen_clr = reg2hw.cpu_regwen.qe & ~reg2hw.cpu_regwen.q;

  assign hw2reg.cpu_info_ctrl.en.d    = intraip_s2p_i.cpu_info_en_q;
  assign hw2reg.cpu_info_ctrl.index.d = intraip_s2p_i.cpu_info_idx_q;
  assign intraip_p2s_o.cpu_info_en_set =
      reg2hw.cpu_info_ctrl.en.qe & reg2hw.cpu_info_ctrl.en.q;
  assign intraip_p2s_o.cpu_info_en_clr =
      reg2hw.cpu_info_ctrl.en.qe & ~reg2hw.cpu_info_ctrl.en.q;
  assign intraip_p2s_o.cpu_info_idx_we = reg2hw.cpu_info_ctrl.index.qe;
  assign intraip_p2s_o.cpu_info_idx_wd = reg2hw.cpu_info_ctrl.index.q;

  rstmgr_crash_info #(
    .CrashDumpWidth($bits(alert_handler_pkg::alert_crashdump_t))
  ) u_alert_info (
    .clk_i(clk_por),
    .rst_ni(rst_por_n),
    .dump_i(alert_dump_i),
    .dump_capture_i(intraip_s2p_i.alert_dump_capture),
    .slot_sel_i(intraip_s2p_i.alert_info_idx_q),
    .slots_cnt_o(hw2reg.alert_info_attr.d),
    .slot_o(hw2reg.alert_info.d)
  );

  rstmgr_crash_info #(
    .CrashDumpWidth($bits(rv_core_ibex_pkg::cpu_crash_dump_t))
  ) u_cpu_info (
    .clk_i(clk_por),
    .rst_ni(rst_por_n),
    .dump_i(cpu_dump_i),
    .dump_capture_i(intraip_s2p_i.cpu_dump_capture),
    .slot_sel_i(intraip_s2p_i.cpu_info_idx_q),
    .slots_cnt_o(hw2reg.cpu_info_attr.d),
    .slot_o(hw2reg.cpu_info.d)
  );

% if export_rsts:
  ////////////////////////////////////////////////////
  // Exported resets                                //
  ////////////////////////////////////////////////////
  // This partition outputs each exported reset in each of its power domains. The other power
  // domains of an exported reset hold it in reset.
% for intf, eps in export_rsts.items():
  % for ep, rsts in eps.items():
    % for exported in rsts:
<% rst = next(r for r in output_rsts if r['name'] == exported['name']) %>\
      % for d in power_domains:
<% field = f"resets_{intf}_o.rst_{intf}_{ep}_{rst['name']}_n[Domain{d}Sel]" %>\
  assign ${field} =
      ${leaf_dst(rst, rst['name'], d) if d in rst['domains'] else "1'b0"};
      % endfor
    % endfor
  % endfor
% endfor

% endif
<%
  ## The resets that this partition outputs but the other partition produces, and the resets that it
  ## produces for the other partition to output. A top may have neither.
  route_lines = []
  for rst in output_rsts:
    names = [rst['name']] + ([rst['name'] + '_shadowed'] if rst['shadowed'] else [])
    prod_doms = rstmgr_hosted_domains(rst, 'primary')
    for n in names:
      # Each copy has its own output domains, because the shadowed copy goes only where a module
      # uses it.
      out_doms = rstmgr_out_domains(rst, 'primary', n)
      other_out = rstmgr_out_domains(rst, 'secondary', n)
      out_arr = bool(out_doms) and rstmgr_is_array(out_doms, power_domains)
      for d in out_doms:
        if d not in prod_doms:
          osel = f"[Domain{d}Sel]" if out_arr else ""
          lhs = f"resets_o.rst_{n}_n{osel}"
          rhs = f"intraip_s2p_i.rst_{n}_n_{d.lower()}"
          line = f"  assign {lhs} = {rhs};"
          route_lines.append(line if len(line) <= 100 else f"  assign {lhs} =\n      {rhs};")
      for d in prod_doms:
        if d in other_out:
          route_lines.append(
              f"  assign intraip_p2s_o.rst_{n}_n_{d.lower()} = {leaf_dst(rst, n, d)};")
%>\
% if route_lines:
  ////////////////////////////////////////////////////
  // Routing. This partition outputs the resets of the power domain that powers down.
  ////////////////////////////////////////////////////
% for line in route_lines:
${line}
% endfor
% endif

  ////////////////////////////////////////////////////
  // Routing. This partition outputs all the reset asserted indications.
  ////////////////////////////////////////////////////
% for rst in output_rsts:
<%
names = [rst['name']] + ([rst['name'] + '_shadowed'] if rst['shadowed'] else [])
prod_doms = rstmgr_hosted_domains(rst, 'primary')
out_arr = rstmgr_is_array(rst['domains'], power_domains)
%>\
  % for n in names:
    % for d in rst['domains']:
<% osel = f"[Domain{d}Sel]" if out_arr else "" %>\
      % if d not in prod_doms:
        % if len(f"  assign rst_en_o.{n}{osel} = intraip_s2p_i.rst_en_{n}_{d.lower()};") <= 100:
  assign rst_en_o.${n}${osel} = intraip_s2p_i.rst_en_${n}_${d.lower()};
        % else:
  assign rst_en_o.${n}${osel} =
      intraip_s2p_i.rst_en_${n}_${d.lower()};
        % endif
      % endif
    % endfor
  % endfor
% endfor

  ////////////////////////////////////////////////////
  // Assertions                                     //
  ////////////////////////////////////////////////////

  `ASSERT_INIT(ParameterMatch_A, NumHwResets == pwrmgr_pkg::HwResetWidth)


  // output known asserts
  `ASSERT_KNOWN(TlDValidKnownO_A,    tl_o.d_valid  )
  `ASSERT_KNOWN(TlAReadyKnownO_A,    tl_o.a_ready  )
  `ASSERT_KNOWN(AlertsKnownO_A,      alert_tx_o    )
  `ASSERT_KNOWN(ResetsKnownO_A,      resets_o      )
  `ASSERT_KNOWN(RstEnKnownO_A,       rst_en_o      )
% for intf in export_rsts:
  `ASSERT_KNOWN(${intf.capitalize()}ResetsKnownO_A, resets_${intf}_o )
% endfor

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule // rstmgr_part_primary
