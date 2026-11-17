// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Secondary partition of the split reset manager.
//
// The secondary partition hosts:
//  - the reset roots (por, lc source and sys source),
//  - the POR handling of each power domain,
//  - the leaf resets of the always-on side,
//  - the record of ERR_CODE and the reset reasons of RESET_INFO.
// It receives the always-on clock of its own power domain. Every other clock enters the primary
// partition, which forwards the clocks that this partition uses.
//  - The bus clock, for the consistency checks of its leaf resets and the record of ERR_CODE.
//  - The POR clock, for its reset controllers and RESET_INFO.
//  - The clocks of some of its leaf resets.
// This partition drives the always-on resets directly. Thus they stay out of reset while the power
// domain of the primary partition is off.
`include "prim_assert.sv"

<%
from topgen.lib import Name
from ipgen.manager_split import (rstmgr_clocks, rstmgr_hosted_domains, rstmgr_is_array,
                                 rstmgr_out_domains, rstmgr_routed_rsts, rstmgr_rst_en_routed,
                                 rstmgr_routed_roots)
split_clks = rstmgr_clocks(clk_freqs, leaf_rsts, rst_ni)
# The clocks that this partition uses, the ones that it receives (ports), and the ones that it gets
# from the primary partition (forwarded).
secondary_clk_names = split_clks.secondary
secondary_port_clk_names = split_clks.ports['secondary']
secondary_fwd_clk_names = split_clks.forwarded['secondary']
# One error flag per leaf instance that this partition hosts (a shadowed leaf has two instances).
n_err = sum((2 if r['shadowed'] else 1) *
            len(rstmgr_hosted_domains(r, 'secondary'))
            for r in leaf_rsts)
PART = 'secondary'
OUT = 'resets_secondary_o'
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
# The state of the reset manager is reset by a leaf that it generates itself, chosen by profile
# (its parent root), variant (power domain) and partition, on the source of the clock that the
# state runs on, so that the state's clock and reset are paired by construction. Generation stops
# if exactly one such leaf does not exist.
off_domains = [d for d in power_domains if d != 'Aon']
assert len(off_domains) == 1, \
    f"the reset manager expects one power domain besides Aon, not {off_domains}"
def state_reset(parent, variant, clock):
    hits = [r for r in leaf_rsts if r['parent'] == parent and r['clock'] == clock and
            variant in rstmgr_hosted_domains(r, PART)]
    if len(hits) != 1:
        raise ValueError(f"The {PART} partition of the reset manager needs exactly one leaf reset "
                         f"with parent {parent}, in power domain {variant}, on the clock {clock}, "
                         f"for its own state; it has {[r['name'] for r in hits]}. Add "
                         f"the reset, or request that variant of it, in the top's configuration.")
    return leaf_dst(hits[0], hits[0]['name'], variant)
%>\
module rstmgr_part_secondary
  import rstmgr_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter bit SecCheck = 1,
  parameter int SecMaxSyncDelay = 2
) (
  // Secondary partition clocks and resets
  input rst_ni,
% for clk in secondary_port_clk_names:
  input clk_${clk}_i,
% endfor
  input rst_por_ni,

  // Scan signals. They come from the DFT source in this partition's power domain, and go on to the
  // primary partition in intraip_s2p_o.
  input prim_mubi_pkg::mubi4_t scanmode_i,
  input scan_rst_ni,

  // POR input
  input [PowerDomains-1:0] por_n_i,

  // pwrmgr interface
  input pwrmgr_pkg::pwr_rst_req_t pwr_i,
  output pwrmgr_pkg::pwr_rst_rsp_t pwr_o,


  // Reset outputs of this partition
  output rstmgr_out_secondary_t resets_secondary_o,

  // inter-partition signalling
  output intraip_s2p_t intraip_s2p_o,
  input intraip_p2s_t intraip_p2s_i
);

  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  // The clocks that this partition uses and does not receive come from the primary partition.
  //  - intraip_p2s_i.clk: the bus clock, for the consistency checks of the leaf resets and the
  //    record of ERR_CODE.
  //  - intraip_p2s_i.clk_por: the POR clock, for the reset controllers and RESET_INFO.
  //  - The clocks of some leaf resets.

  // The leaf resets that this partition generates but does not output. They only cross to the
  // primary partition.
% for net in local_leaves(output_rsts):
  logic ${net};
% endfor

  // receive POR and stretch
  // The por is at first stretched and synced on clk_aon
  logic [PowerDomains-1:0] rst_por_aon_n;
  // The roots and their reset asserted indications exist for every power domain. The por_aon reset
  // takes the roots and indications of its own power domains, in the shape of the output structs.
  mubi4_t [PowerDomains-1:0] rst_en_por_aon;

  ////////////////////////////////////////////////////
  // Scan mode of the POR roots                     //
  ////////////////////////////////////////////////////

  // The scan mode, with one copy for the root of each power domain. With AsyncOn(0),
  // prim_mubi4_sync only buffers it. Its clock and reset serve only its assertion.
  prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por_scanmode;
  prim_mubi4_sync #(
    .NumCopies(PowerDomains),
    .AsyncOn(0)
  ) u_por_scanmode_sync (
    .clk_i(intraip_p2s_i.clk),
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o(por_scanmode)
  );

% for domain in power_domains:
<%  sel = f"Domain{domain}Sel"
title = f"POR root of the {domain} power domain" %>\
  ////////////////////////////////////////////////////
  // ${title.ljust(46)} //
  ////////////////////////////////////////////////////

  % if domain == 'Aon':
  // The root of the Aon power domain is the stretched POR.
  % else:
  // The root of the ${domain} power domain combines the always-on root and the POR (power good) of
  // the ${domain} power domain. It does not release before the always-on root.
  % endif
  % if domain == 'Aon':
  rstmgr_por u_rst_por_aon (
    .clk_i(clk_aon_i),
    .rst_ni(por_n_i[${sel}]),
    .scan_rst_ni(scan_rst_ni),
    .scanmode_i(prim_mubi_pkg::mubi4_test_true_strict(por_scanmode[${sel}])),
    .rst_no(rst_por_aon_n[${sel}])
  );
  % else:
  logic rst_por_${domain.lower()}_premux;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_por_${domain.lower()}_sync (
    .clk_i(clk_aon_i),
    .rst_ni(rst_por_aon_n[DomainAonSel] & por_n_i[${sel}]),
    .d_i(1'b1),
    .q_o(rst_por_${domain.lower()}_premux)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_por_${domain.lower()}_mux (
    .clk0_i(rst_por_${domain.lower()}_premux),
    .clk1_i(scan_rst_ni),
    .sel_i(prim_mubi_pkg::mubi4_test_true_strict(por_scanmode[${sel}])),
    .clk_o(rst_por_aon_n[${sel}])
  );
  % endif

  // The reset asserted indication of the ${domain} root, for the alert handler.
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_rst_por_${domain.lower()}_en_sender (
    .clk_i(clk_aon_i),
    .rst_ni(rst_por_aon_n[${sel}]),
    .mubi_i(MuBi4False),
    .mubi_o(rst_en_por_aon[${sel}])
  );

% endfor
<%
por_aon = [r for r in output_rsts if r['name'] == 'por_aon'][0]
por_aon_unused = [d for d in power_domains if d not in por_aon['domains']]
%>\
% for d in por_aon['domains']:
  % if d in rstmgr_out_domains(por_aon, PART):
  assign ${leaf_dst(por_aon, 'por_aon', d)} = rst_por_aon_n[Domain${d}Sel];
  % endif
  assign ${en_dst(por_aon, 'por_aon', d)} = rst_en_por_aon[Domain${d}Sel];
% endfor
% if por_aon_unused:
  // In these power domains, nothing uses the reset asserted indication of por_aon.
  logic unused_rst_en_por_aon;
  assign unused_rst_en_por_aon = ^{${', '.join(f"rst_en_por_aon[Domain{d}Sel]" for d in por_aon_unused)}};
% endif

  logic clk_por;
  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_por_clk_buf (
    .clk_i(intraip_p2s_i.clk_por),
    .clk_o(clk_por)
  );

  logic rst_por_n;
  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_por_rst_buf (
    .clk_i(rst_por_ni),
    .clk_o(rst_por_n)
  );

  ////////////////////////////////////////////////////
  // Source resets in the system                    //
  // These are hardcoded and not directly used.     //
  // Instead they act as async reset roots.         //
  ////////////////////////////////////////////////////

  // The lc and sys source controllers share the POR roots as their parents. An lc reset does not
  // imply a sys reset structurally. The power manager requests both together, except for a
  // non-debug-module reset with debug enabled, which resets the lc domain alone.

  logic [PowerDomains-1:0] rst_lc_src_n;
  logic [PowerDomains-1:0] rst_sys_src_n;

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] rst_ctrl_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_ctrl_scanmode_sync (
    .clk_i (clk_por),
    .rst_ni (rst_por_n),
    .mubi_i(scanmode_i),
    .mubi_o(rst_ctrl_scanmode)
  );

  // lc reset sources
  rstmgr_ctrl u_lc_src (
    .clk_i (clk_por),
    .scanmode_i(prim_mubi_pkg::mubi4_test_true_strict(rst_ctrl_scanmode[0])),
    .scan_rst_ni(scan_rst_ni),
    .rst_req_i(pwr_i.rst_lc_req),
    .rst_parent_ni(rst_por_aon_n),
    .rst_no(rst_lc_src_n)
  );

  // sys reset sources
  rstmgr_ctrl u_sys_src (
    .clk_i (clk_por),
    .scanmode_i(prim_mubi_pkg::mubi4_test_true_strict(rst_ctrl_scanmode[0])),
    .scan_rst_ni(scan_rst_ni),
    .rst_req_i(pwr_i.rst_sys_req),
    .rst_parent_ni(rst_por_aon_n),
    .rst_no(rst_sys_src_n)
  );

  assign pwr_o.rst_lc_src_n = rst_lc_src_n;
  assign pwr_o.rst_sys_src_n = rst_sys_src_n;

  ////////////////////////////////////////////////////
  // Errors of this partition's leaf resets         //
  ////////////////////////////////////////////////////
% if n_err:
  logic [${n_err-1}:0] cnsty_chk_errs;
  logic [${n_err-1}:0] fsm_errs;
% endif

  ////////////////////////////////////////////////////
  // Leaf resets of the secondary partition         //
  // The primary partition generates every other    //
  // leaf reset.                                    //
  ////////////////////////////////////////////////////
<% err_idx = 0 %>\
% for rst in leaf_rsts:
<%
names = [rst['name']]
if rst['shadowed']:
  names.append(f"{rst['name']}_shadowed")
hosted = rstmgr_hosted_domains(rst, 'secondary')
assert not hosted or rst['clock'] in secondary_clk_names, (
    f"reset {rst['name']} is driven by the secondary partition, which has no port for its clock {rst['clock']}")
arr = bool(hosted) and rstmgr_is_array(hosted, power_domains)
# The always-on clock is an input port. The clocks forwarded by the primary partition are fields of
# intraip_p2s_i.
leaf_clk = (f"intraip_p2s_i.clk_{rst['clock']}" if rst['clock'] in secondary_fwd_clk_names
            else f"clk_{rst['clock']}_i")
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
    .clk_i(intraip_p2s_i.clk),
    .rst_ni,
    .leaf_clk_i(${leaf_clk}),
    .parent_rst_ni(rst_${rst['parent']}_n[Domain${domain}Sel]),
<% assert not rst['sw'], f"secondary leaf {rst['name']} cannot be software resettable" %>\
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_ni),
    .scanmode_i(scanmode_i),
    .rst_en_o(${en_dst(rst, name, domain)}),
    .leaf_rst_o(${leaf_dst(rst, name, domain)}),
    .err_o(cnsty_chk_errs[${err_idx}]),
    .fsm_err_o(fsm_errs[${err_idx}])
  );
<% err_idx += 1 %>\
        % if names[0]!=rst_ni:
  // The assertion uses _ERR rather than _ALERT on purpose, as this partition has no alert. The FSM
  // error leaves this partition through intraip_s2p_o.fsm_err_q, and the primary partition turns it
  // into its fatal alert.
  if (SecCheck) begin : gen_d${domain.lower()}_${name}_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(
    D${domain.capitalize()}${rst_name_camel}FsmCheck_A,
    u_d${domain.lower()}_${name}.gen_rst_chk.u_rst_chk.u_state_regs,
    intraip_s2p_o.fsm_err_q, 0, 2, intraip_p2s_i.clk, !rst_ni)
  end
        % endif
      % endfor
    % endfor
  % endif
% endfor

  ////////////////////////////////////////////////////
  // Signalling to the primary partition            //
  ////////////////////////////////////////////////////
% for root, domain in rstmgr_routed_roots(leaf_rsts):
  assign intraip_s2p_o.rst_${root}_n_${domain.lower()} = rst_${root}_n[Domain${domain}Sel];
% endfor
  assign intraip_s2p_o.pwr_rst_lc_req       = pwr_i.rst_lc_req;
  assign intraip_s2p_o.pwr_rst_sys_req      = pwr_i.rst_sys_req;
  assign intraip_s2p_o.pwr_reset_cause      = pwr_i.reset_cause;

  // The scan signals enter this partition only. The primary partition gets them from here.
  assign intraip_s2p_o.scanmode             = scanmode_i;
  assign intraip_s2p_o.scan_rst_n           = scan_rst_ni;

  ////////////////////////////////////////////////////
  // Reset info (RESET_INFO)                        //
  ////////////////////////////////////////////////////

  // RESET_INFO is external (hwext). This partition keeps the reset reasons in the always-on power
  // domain, on the POR clock and the POR reset. Thus the reasons operate the same as register
  // fields. The POR sets the POR bit, and only the POR resets the reasons. The primary partition
  // reads the reasons and forwards the software writes. Software clears a reason when it writes 1
  // to it (rw1c). The hardware sets a reason. If the hardware sets a reason and software clears it
  // in the same cycle, the set wins.
  logic pwrmgr_rst_req, rst_hw_req, rst_low_power;
  assign pwrmgr_rst_req = |pwr_i.rst_lc_req || |pwr_i.rst_sys_req;
  // A reset reason is only valid if the related processing element is also reset.
  assign rst_hw_req    = pwrmgr_rst_req && (pwr_i.reset_cause == pwrmgr_pkg::HwReq);
  assign rst_low_power = pwrmgr_rst_req && (pwr_i.reset_cause == pwrmgr_pkg::LowPwrEntry);

  rstmgr_reg_pkg::rstmgr_hw2reg_reset_info_reg_t reset_info_q;
  rstmgr_reg_pkg::rstmgr_reg2hw_reset_info_reg_t reset_info_wr;
  assign reset_info_wr = intraip_p2s_i.reset_info;

<% info_rst = state_reset('por_aon', 'Aon', por_clk) %>\
  // RESET_INFO's storage runs on the POR clock, and is reset by the POR of this power domain on
  // that clock (${info_rst}).
  always_ff @(posedge clk_por or negedge ${info_rst}) begin
    if (!${info_rst}) begin
      reset_info_q.por.d            <= 1'b1;
      reset_info_q.low_power_exit.d <= 1'b0;
      reset_info_q.sw_reset.d       <= 1'b0;
      reset_info_q.hw_req.d         <= '0;
    end else begin
      if (reset_info_wr.por.qe && reset_info_wr.por.q) begin
        reset_info_q.por.d <= 1'b0;
      end
      if (reset_info_wr.low_power_exit.qe && reset_info_wr.low_power_exit.q) begin
        reset_info_q.low_power_exit.d <= 1'b0;
      end
      if (reset_info_wr.sw_reset.qe && reset_info_wr.sw_reset.q) begin
        reset_info_q.sw_reset.d <= 1'b0;
      end
      if (reset_info_wr.hw_req.qe) begin
        reset_info_q.hw_req.d <= reset_info_q.hw_req.d & ~reset_info_wr.hw_req.q;
      end
      if (rst_low_power) begin
        reset_info_q.low_power_exit.d <= 1'b1;
      end
      // A software reset request triggers the same response as a hardware one, but is recorded
      // apart from it.
      if (rst_hw_req) begin
        reset_info_q.sw_reset.d <=
            prim_mubi_pkg::mubi4_test_true_strict(intraip_p2s_i.sw_rst_req) ||
            reset_info_q.sw_reset.d;
        reset_info_q.hw_req.d   <= pwr_i.rstreqs | reset_info_q.hw_req.d;
      end
    end
  end

  assign intraip_s2p_o.reset_info = reset_info_q;
  // The store of the ERR_CODE CSR, whose register type is hwext. One bit per field:
  //  - REG_INTG_ERR: the integrity error of the register file.
  //  - RESET_CONSISTENCY_ERR: the consistency errors of the leaves of both partitions.
  //  - FSM_ERR: the FSM errors of the leaves of both partitions.
  // They are kept here, in the secondary partition, as it is always in the Aon power domain. This
  // keeps them through a deep sleep cycle, and captures tampering with the Aon resets, under these
  // requirements:
  //  - The checkers' clock must run until their resets assert. A detection made while it is off,
  //    on entering deep sleep or later, is lost.
  //  - While the primary partition's power domain is off, its isolation must clamp the error bits
  //    of intraip_p2s_i to 0. Otherwise these bits would latch a false error.
  //  - The record runs on the bus clock that the primary partition forwards, the clock on which
  //    that partition detects its errors, so these bits need no synchronizer.
  // Note: the reset that an escalation triggers must clear these bits, or the alert would fire
  // again after the escalation.
  logic cnsty_chk_err, fsm_err;
  logic reg_intg_err_q, cnsty_chk_err_q, fsm_err_q;
% if n_err:
  assign cnsty_chk_err = |cnsty_chk_errs || intraip_p2s_i.cnsty_chk_err;
  assign fsm_err       = |fsm_errs || intraip_p2s_i.fsm_err;
% else:
  assign cnsty_chk_err = intraip_p2s_i.cnsty_chk_err;
  assign fsm_err       = intraip_p2s_i.fsm_err;
% endif

<% err_rst = state_reset('lc_src', 'Aon', bus_clk) %>\
  // The record uses the bus clock, because the primary partition detects these errors on the bus
  // clock. Thus the record needs no synchronizer. The lc reset of this power domain on that clock
  // resets the record. Thus an escalation's reset clears the record, but a deep sleep does not.
  // That reset is ${err_rst}.
  logic err_code_rst_n;
  assign err_code_rst_n = ${err_rst};
  always_ff @(posedge intraip_p2s_i.clk or negedge err_code_rst_n) begin
    if (!err_code_rst_n) begin
      reg_intg_err_q  <= 1'b0;
      cnsty_chk_err_q <= 1'b0;
      fsm_err_q       <= 1'b0;
    end else begin
      reg_intg_err_q  <= reg_intg_err_q || intraip_p2s_i.reg_intg_err;
      cnsty_chk_err_q <= cnsty_chk_err_q || cnsty_chk_err;
      fsm_err_q       <= fsm_err_q || fsm_err;
    end
  end

  assign intraip_s2p_o.reg_intg_err_q         = reg_intg_err_q;
  assign intraip_s2p_o.cnsty_chk_err_q        = cnsty_chk_err_q;
  assign intraip_s2p_o.fsm_err_q              = fsm_err_q;

  `ASSERT(RegIntgErrRecordSticky_A, reg_intg_err_q |=> reg_intg_err_q, intraip_p2s_i.clk,
          !err_code_rst_n)
  `ASSERT(CnstyChkErrRecordSticky_A, cnsty_chk_err_q |=> cnsty_chk_err_q, intraip_p2s_i.clk,
          !err_code_rst_n)
  `ASSERT(FsmErrRecordSticky_A, fsm_err_q |=> fsm_err_q, intraip_p2s_i.clk,
          !err_code_rst_n)
% if not n_err:
  // Without leaves, this partition does not use the parameters of the leaves, or the clocks that
  // only leaves use.
  logic unused_leaf_cfg;
  assign unused_leaf_cfg = ^{SecCheck, SecMaxSyncDelay${''.join(f", intraip_p2s_i.clk_{c}" for c in secondary_clk_names if c != 'aon')}};
% endif

  ////////////////////////////////////////////////////
  // Assertions                                     //
  ////////////////////////////////////////////////////
  `ASSERT_KNOWN(PwrKnownO_A,         pwr_o, intraip_p2s_i.clk, !rst_ni)
  ////////////////////////////////////////////////////
  // Routing. This partition outputs the resets of the modules of the always-on power domain.
  ////////////////////////////////////////////////////
% for rst in output_rsts:
<%
names = [rst['name']] + ([rst['name'] + '_shadowed'] if rst['shadowed'] else [])
prod_doms = rstmgr_hosted_domains(rst, 'secondary')
%>\
  % for n in names:
<%
# Each copy has its own output domains, because the shadowed copy goes only where a module uses it.
out_doms = rstmgr_out_domains(rst, 'secondary', n)
other_out = rstmgr_out_domains(rst, 'primary', n)
out_arr = bool(out_doms) and rstmgr_is_array(out_doms, power_domains)
%>\
    % for d in out_doms:
<% osel = f"[Domain{d}Sel]" if out_arr else "" %>\
<% lhs = f"resets_secondary_o.rst_{n}_n{osel}"
rhs = f"intraip_p2s_i.rst_{n}_n_{d.lower()}" %>\
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
  assign intraip_s2p_o.rst_${n}_n_${d.lower()} = ${leaf_dst(rst, n, d)};
      % endif
    % endfor
  % endfor
% endfor

  // The reset asserted indications that this partition generates go to the primary partition, which
  // outputs them. Each leaf drives its field of intraip_s2p_o directly.

  `ASSERT_KNOWN(ResetsKnownO_A,      resets_secondary_o, intraip_p2s_i.clk, !rst_ni)
  `ASSERT_KNOWN(IntraipKnownO_A,   intraip_s2p_o, intraip_p2s_i.clk, !rst_ni)
endmodule // rstmgr_part_secondary
