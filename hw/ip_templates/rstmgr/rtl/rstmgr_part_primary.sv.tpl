// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Primary partition of the split reset manager.
//
// The primary partition hosts:
//  - the register file and the alerts (ERR_CODE and RESET_INFO are external: the secondary
//    partition keeps their state),
//  - the crash dump capture (ALERT_INFO and CPU_INFO),
//  - the leaf resets that the secondary partition does not host.

`include "prim_assert.sv"

<%
from topgen.lib import Name
from ipgen.manager_split import (rstmgr_clocks, rstmgr_hosted_domains, rstmgr_is_array,
                                 rstmgr_out_domains, rstmgr_routed_roots, rstmgr_routed_rsts)
split_clks = rstmgr_clocks(clk_freqs, leaf_rsts, rst_ni)
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

  // software initiated reset request
  output mubi4_t sw_rst_req_o,

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

  // The leaf resets that this partition generates but does not output. They only cross to the
  // secondary partition.
% for net in local_leaves(output_rsts):
  logic ${net};
% endfor

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
    .clk_por_i  (clk_por),
    .rst_por_ni (rst_por_n),
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

  // consistency sparse fsm errors

  // ERR_CODE is external, so the register file keeps no state for it. The errors of this partition
  // go to the secondary partition, which keeps the record of all of them in the always-on power
  // domain. ERR_CODE and the alerts read that record.
  assign intraip_p2s_o.reg_intg_err  = reg_intg_err;
  // The clocks that the secondary partition uses, which enter this partition only.
  assign intraip_p2s_o.clk     = clk_i;
  assign intraip_p2s_o.clk_por = clk_por_i;
% for clk in secondary_fwd_clk_names:
  assign intraip_p2s_o.clk_${clk} = clk_${clk}_i;
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

  // The secondary partition generates the source resets (lc and sys).


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

  logic rst_hw_req;
  logic rst_low_power;
  logic pwrmgr_rst_req;

  // there is a valid reset request from pwrmgr
  assign pwrmgr_rst_req = |intraip_s2p_i.pwr_rst_lc_req || |intraip_s2p_i.pwr_rst_sys_req;

  // a reset reason is only valid if the related processing element is also reset.
  // In the future, if ever there are multiple processing elements, this code here
  // must be updated to account for each individual core.
  assign rst_hw_req    = pwrmgr_rst_req &
                         (intraip_s2p_i.pwr_reset_cause == pwrmgr_pkg::HwReq);
  assign rst_low_power = pwrmgr_rst_req &
                         (intraip_s2p_i.pwr_reset_cause == pwrmgr_pkg::LowPwrEntry);

  // software initiated reset request
  assign sw_rst_req_o = prim_mubi_pkg::mubi4_t'(reg2hw.reset_req.q);

  // when pwrmgr reset request is received (reset is imminent), clear software
  // request so we are not in an infinite reset loop.
  assign hw2reg.reset_req.de = pwrmgr_rst_req;
  assign hw2reg.reset_req.d  = prim_mubi_pkg::MuBi4False;

  // RESET_INFO is external (hwext). The secondary partition keeps the reset reasons in the
  // always-on power domain, so that they survive a deep sleep. This partition reads them, and
  // forwards the software writes and the software reset request that SW_RESET records.
  assign hw2reg.reset_info        = intraip_s2p_i.reset_info;
  assign intraip_p2s_o.reset_info = reg2hw.reset_info;
  assign intraip_p2s_o.sw_rst_req = sw_rst_req_o;

  ////////////////////////////////////////////////////
  // Crash info capture                             //
  ////////////////////////////////////////////////////

  logic dump_capture;
  assign dump_capture =  rst_hw_req | rst_low_power;

  // halt dump capture once we hit particular conditions
  logic dump_capture_halt;
  assign dump_capture_halt = rst_hw_req;

  rstmgr_crash_info #(
    .CrashDumpWidth($bits(alert_handler_pkg::alert_crashdump_t))
  ) u_alert_info (
    .clk_i(clk_por),
    .rst_ni(rst_por_n),
    .dump_i(alert_dump_i),
    .dump_capture_i(dump_capture & reg2hw.alert_info_ctrl.en.q),
    .slot_sel_i(reg2hw.alert_info_ctrl.index.q),
    .slots_cnt_o(hw2reg.alert_info_attr.d),
    .slot_o(hw2reg.alert_info.d)
  );

  rstmgr_crash_info #(
    .CrashDumpWidth($bits(rv_core_ibex_pkg::cpu_crash_dump_t))
  ) u_cpu_info (
    .clk_i(clk_por),
    .rst_ni(rst_por_n),
    .dump_i(cpu_dump_i),
    .dump_capture_i(dump_capture & reg2hw.cpu_info_ctrl.en.q),
    .slot_sel_i(reg2hw.cpu_info_ctrl.index.q),
    .slots_cnt_o(hw2reg.cpu_info_attr.d),
    .slot_o(hw2reg.cpu_info.d)
  );

  // once dump is captured, no more information is captured until
  // re-enabled by software.
  assign hw2reg.alert_info_ctrl.en.d  = 1'b0;
  assign hw2reg.alert_info_ctrl.en.de = dump_capture_halt;
  assign hw2reg.cpu_info_ctrl.en.d  = 1'b0;
  assign hw2reg.cpu_info_ctrl.en.de = dump_capture_halt;

% if export_rsts:
  ////////////////////////////////////////////////////
  // Exported resets                                //
  ////////////////////////////////////////////////////
% for intf, eps in export_rsts.items():
  % for ep, rsts in eps.items():
    % for rst in rsts:
<% assert len(rstmgr_hosted_domains(next(r for r in output_rsts if r['name'] == rst['name']), 'primary')) == len(power_domains), f"exported reset {rst['name']} must be hosted by the primary partition for every power domain" %>\
  assign resets_${intf}_o.rst_${intf}_${ep}_${rst['name']}_n = resets_o.rst_${rst['name']}_n;
    % endfor
  % endfor
% endfor

% endif
  ////////////////////////////////////////////////////
  // Assertions                                     //
  ////////////////////////////////////////////////////

  `ASSERT_INIT(ParameterMatch_A, NumHwResets == pwrmgr_pkg::HwResetWidth)


  // output known asserts
  `ASSERT_KNOWN(TlDValidKnownO_A,    tl_o.d_valid  )
  `ASSERT_KNOWN(TlAReadyKnownO_A,    tl_o.a_ready  )
  `ASSERT_KNOWN(AlertsKnownO_A,      alert_tx_o    )
  ////////////////////////////////////////////////////
  // Routing. This partition outputs the resets of the power domain that powers down.
  ////////////////////////////////////////////////////
% for rst in output_rsts:
<%
names = [rst['name']] + ([rst['name'] + '_shadowed'] if rst['shadowed'] else [])
prod_doms = rstmgr_hosted_domains(rst, 'primary')
%>\
  % for n in names:
<%
# Each copy has its own output domains, because the shadowed copy goes only where a module uses it.
out_doms = rstmgr_out_domains(rst, 'primary', n)
other_out = rstmgr_out_domains(rst, 'secondary', n)
out_arr = bool(out_doms) and rstmgr_is_array(out_doms, power_domains)
%>\
    % for d in out_doms:
<% osel = f"[Domain{d}Sel]" if out_arr else "" %>\
<% lhs = f"resets_o.rst_{n}_n{osel}"
rhs = f"intraip_s2p_i.rst_{n}_n_{d.lower()}" %>\
      % if d not in prod_doms:
        % if len(f"  assign {lhs} = {rhs};") <= 100:
  assign ${lhs} = ${rhs};
        % else:
  assign ${lhs} =
      ${rhs};
        % endif
      % endif
    % endfor
    % for d in prod_doms:
      % if d in other_out:
  assign intraip_p2s_o.rst_${n}_n_${d.lower()} = ${leaf_dst(rst, n, d)};
      % endif
    % endfor
  % endfor
% endfor

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

  `ASSERT_KNOWN(ResetsKnownO_A,      resets_o      )
  `ASSERT_KNOWN(RstEnKnownO_A,       rst_en_o      )
% for intf in export_rsts:
  `ASSERT_KNOWN(${intf.capitalize()}ResetsKnownO_A, resets_${intf}_o )
% endfor

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule // rstmgr_part_primary
