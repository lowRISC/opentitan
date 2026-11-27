// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Secondary partition of the split reset manager.
//
// The secondary partition hosts:
//  - the reset roots (por, lc source and sys source),
//  - the POR handling of each power domain,
//  - the leaf resets of the always-on power domain,
//  - the state of the registers that are external in the primary partition's register file:
//    RESET_REQ, which it sends to the power manager, RESET_INFO, the dump controls ALERT_INFO_CTRL
//    and CPU_INFO_CTRL with their locks ALERT_REGWEN and CPU_REGWEN, and the record of ERR_CODE,
//  - the decisions to capture the crash dumps.
// It receives the always-on clock of its own power domain. Every other clock enters the primary
// partition, which forwards the clocks that this partition uses.
//  - The bus clock, for the consistency checks of its leaf resets, RESET_REQ, the locks and the
//    record of ERR_CODE.
//  - The POR clock, for its reset controllers, RESET_INFO and the dump controls.
//  - The clocks of some of its leaf resets.
// This partition drives the always-on resets directly. Thus they stay out of reset while the power
// domain of the primary partition is off.
`include "prim_assert.sv"

<%
from topgen.lib import Name
from ipgen.manager_split import (rstmgr_clocks, rstmgr_hosted_domains, rstmgr_is_array,
                                 rstmgr_out_domains, rstmgr_routed_roots)
split_clks = rstmgr_clocks(clk_freqs, leaf_rsts, rst_ni, aon_clock)
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
# The partition's own logic uses its own leaves directly: the POR leaf on the POR clock and the lc
# leaf on the bus clock. They are not taken back through the top.
info_rst = state_reset('por_aon', 'Aon', por_clk)
reg_rst = state_reset('lc_src', 'Aon', bus_clk)
%>\
module rstmgr_part_secondary
  import rstmgr_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter bit SecCheck = 1,
  parameter int SecMaxSyncDelay = 2
) (
  // Secondary partition clocks and resets. rst_aon_ni completes the partition's primary clocking
  // pair, and is not used. The partition's own logic uses its own always-on POR and lc leaves.
  input rst_aon_ni,
% for clk in secondary_port_clk_names:
  input clk_${clk}_i,
% endfor

  // Scan signals. They come from the DFT source in this partition's power domain, and go on to the
  // primary partition in intraip_s2p_o.
  input prim_mubi_pkg::mubi4_t scanmode_i,
  input scan_rst_ni,

  // POR input
  input [PowerDomains-1:0] por_n_i,

  // pwrmgr interface
  input pwrmgr_pkg::pwr_rst_req_t pwr_i,
  output pwrmgr_pkg::pwr_rst_rsp_t pwr_o,

  // software initiated reset request
  output prim_mubi_pkg::mubi4_t sw_rst_req_o,


  // Reset outputs of this partition
  output rstmgr_out_secondary_t resets_secondary_o,

  // inter-partition signalling
  output intraip_s2p_t intraip_s2p_o,
  input intraip_p2s_t intraip_p2s_i
);

  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  // The lc reset of this power domain on the bus clock. It resets the registers, the consistency
  // checks and the assertions on the bus clock.
  logic reg_rst_n;
  assign reg_rst_n = ${reg_rst};

  // The clocks that this partition uses and does not receive come from the primary partition.
  //  - intraip_p2s_i.clk: the bus clock, for the consistency checks of the leaf resets and the
  //    record of ERR_CODE.
  //  - intraip_p2s_i.clk_por: the POR clock, for the reset controllers and RESET_INFO.
  //  - The clocks of some leaf resets.

% if local_leaves(output_rsts):
  // The leaf resets that this partition generates but does not output. They only cross to the
  // primary partition.
  % for net in local_leaves(output_rsts):
  logic ${net};
  % endfor
% endif

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
    .rst_ni(reg_rst_n),
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
    .rst_ni (${info_rst}),
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
  // The FSM assertions of these leaves use _ERR rather than _ALERT on purpose, as this partition
  // has no alert. The FSM errors leave this partition through intraip_s2p_o.fsm_err_q, and the
  // primary partition turns them into its fatal alert.
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
    .rst_ni(reg_rst_n),
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
  if (SecCheck) begin : gen_d${domain.lower()}_${name}_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(
    D${domain.capitalize()}${rst_name_camel}FsmCheck_A,
    u_d${domain.lower()}_${name}.gen_rst_chk.u_rst_chk.u_state_regs,
    intraip_s2p_o.fsm_err_q, 0, 2, intraip_p2s_i.clk, !reg_rst_n)
  end
        % endif
      % endfor
    % endfor
  % endif
% endfor

  ////////////////////////////////////////////////////
  // Signalling to the primary partition            //
  ////////////////////////////////////////////////////
<% routed = [(f"rst_{r}_n_{d.lower()}", r, d) for r, d in rstmgr_routed_roots(leaf_rsts)] %>\
<% routed_w = max([len(n) for n, _, _ in routed], default=0) %>\
% for name, root, domain in routed:
  assign intraip_s2p_o.${name.ljust(routed_w)} = rst_${root}_n[Domain${domain}Sel];
% endfor

  // The scan signals enter this partition only. The primary partition gets them from here.
  assign intraip_s2p_o.scanmode   = scanmode_i;
  assign intraip_s2p_o.scan_rst_n = scan_rst_ni;

  ////////////////////////////////////////////////////
  // Registers kept in the always-on power domain    //
  ////////////////////////////////////////////////////

  // These registers are external (hwext). This partition keeps them in the always-on power domain,
  // so that a deep sleep keeps them, and the primary partition reads them and forwards the software
  // writes. They are in the order of the address map.

  logic pwrmgr_rst_req, rst_hw_req, rst_low_power;
  assign pwrmgr_rst_req = |pwr_i.rst_lc_req || |pwr_i.rst_sys_req;
  // A reset reason is only valid if the related processing element is also reset.
  assign rst_hw_req    = pwrmgr_rst_req && (pwr_i.reset_cause == pwrmgr_pkg::HwReq);
  assign rst_low_power = pwrmgr_rst_req && (pwr_i.reset_cause == pwrmgr_pkg::LowPwrEntry);

  // Two resets serve these registers. The POR of this power domain on the POR clock resets the
  // registers on that clock: RESET_INFO and the dump controls. Only a POR resets them.
  // That reset is ${info_rst}.
  // The lc reset of this power domain on the bus clock resets the registers on the bus clock:
  // RESET_REQ, the locks of the dump controls and the record of ERR_CODE. An escalation's reset
  // clears them, but a deep sleep does not, the same as for the register file.
  // That reset is reg_rst_n, declared at the top of the module.

  // RESET_REQ: the software reset request, which this partition sends to the power manager. When
  // the power manager's reset request arrives, the reset is imminent, so the software request is
  // cleared, to avoid an infinite reset loop. A software write in the same cycle wins, the same as
  // for a register field.
  prim_mubi_pkg::mubi4_t reset_req_q;
  always_ff @(posedge intraip_p2s_i.clk or negedge reg_rst_n) begin
    if (!reg_rst_n) begin
      reset_req_q <= prim_mubi_pkg::MuBi4False;
    end else if (intraip_p2s_i.reset_req_we) begin
      reset_req_q <= intraip_p2s_i.reset_req_wd;
    end else if (pwrmgr_rst_req) begin
      reset_req_q <= prim_mubi_pkg::MuBi4False;
    end
  end

  assign sw_rst_req_o              = reset_req_q;
  assign intraip_s2p_o.reset_req_q = reset_req_q;

  // RESET_INFO: the reset reasons. The POR sets the POR bit. The hardware sets a reason. Software
  // clears a reason when it writes 1 to it (rw1c). If the hardware sets a reason and software
  // clears it in the same cycle, the clear wins, the same as for a register field. So the clears
  // come after the sets below.
  rstmgr_reg_pkg::rstmgr_hw2reg_reset_info_reg_t reset_info_q;
  always_ff @(posedge clk_por or negedge ${info_rst}) begin
    if (!${info_rst}) begin
      reset_info_q.por.d            <= 1'b1;
      reset_info_q.low_power_exit.d <= 1'b0;
      reset_info_q.sw_reset.d       <= 1'b0;
      reset_info_q.hw_req.d         <= '0;
    end else begin
      if (rst_low_power) begin
        reset_info_q.low_power_exit.d <= 1'b1;
      end
      // A software reset request triggers the same response as a hardware one, but is recorded
      // apart from it.
      if (rst_hw_req) begin
        if (prim_mubi_pkg::mubi4_test_true_strict(reset_req_q)) begin
          reset_info_q.sw_reset.d <= 1'b1;
        end
        for (int i = 0; i < rstmgr_reg_pkg::NumHwResets; i++) begin
          if (pwr_i.rstreqs[i]) begin
            reset_info_q.hw_req.d[i] <= 1'b1;
          end
        end
      end
      if (intraip_p2s_i.por_clr) begin
        reset_info_q.por.d <= 1'b0;
      end
      if (intraip_p2s_i.low_power_exit_clr) begin
        reset_info_q.low_power_exit.d <= 1'b0;
      end
      if (intraip_p2s_i.sw_reset_clr) begin
        reset_info_q.sw_reset.d <= 1'b0;
      end
      for (int i = 0; i < rstmgr_reg_pkg::NumHwResets; i++) begin
        if (intraip_p2s_i.hw_req_clr[i]) begin
          reset_info_q.hw_req.d[i] <= 1'b0;
        end
      end
    end
  end

  assign intraip_s2p_o.reset_info_q = reset_info_q;

  // ALERT_REGWEN: the lock of ALERT_INFO_CTRL. A write of 0 clears it (rw0c), and only the reset
  // sets it again. The primary partition's register file reads it, and blocks the writes to
  // ALERT_INFO_CTRL while it is clear.
  logic alert_regwen_q;
  always_ff @(posedge intraip_p2s_i.clk or negedge reg_rst_n) begin
    if (!reg_rst_n) begin
      alert_regwen_q <= 1'b1;
    end else if (intraip_p2s_i.alert_regwen_clr) begin
      alert_regwen_q <= 1'b0;
    end
  end

  assign intraip_s2p_o.alert_regwen_q = alert_regwen_q;

  // ALERT_INFO_CTRL: the control of the alert dump. EN is the enable, so that a deep sleep keeps
  // the dump armed. A hardware reset or a low power entry captures the dump in the primary
  // partition. A hardware reset also clears the enable here, so that no more information is
  // captured until software enables the dump again. A software write in the same cycle wins, the
  // same as for a register field. INDEX selects the word of the dump that ALERT_INFO reads.
  logic alert_info_en_q;
  logic [rstmgr_reg_pkg::IdxWidth-1:0] alert_info_idx_q;
  always_ff @(posedge clk_por or negedge ${info_rst}) begin
    if (!${info_rst}) begin
      alert_info_en_q  <= 1'b0;
      alert_info_idx_q <= '0;
    end else begin
      if (intraip_p2s_i.alert_info_en_set) begin
        alert_info_en_q <= 1'b1;
      end else if (intraip_p2s_i.alert_info_en_clr || rst_hw_req) begin
        alert_info_en_q <= 1'b0;
      end
      if (intraip_p2s_i.alert_info_idx_we) begin
        alert_info_idx_q <= intraip_p2s_i.alert_info_idx_wd;
      end
    end
  end

  assign intraip_s2p_o.alert_info_en_q    = alert_info_en_q;
  assign intraip_s2p_o.alert_info_idx_q   = alert_info_idx_q;
  assign intraip_s2p_o.alert_dump_capture = (rst_hw_req | rst_low_power) & alert_info_en_q;

  // CPU_REGWEN: the lock of CPU_INFO_CTRL, the same as ALERT_REGWEN.
  logic cpu_regwen_q;
  always_ff @(posedge intraip_p2s_i.clk or negedge reg_rst_n) begin
    if (!reg_rst_n) begin
      cpu_regwen_q <= 1'b1;
    end else if (intraip_p2s_i.cpu_regwen_clr) begin
      cpu_regwen_q <= 1'b0;
    end
  end

  assign intraip_s2p_o.cpu_regwen_q = cpu_regwen_q;

  // CPU_INFO_CTRL: the control of the CPU dump, the same as ALERT_INFO_CTRL.
  logic cpu_info_en_q;
  logic [rstmgr_reg_pkg::IdxWidth-1:0] cpu_info_idx_q;
  always_ff @(posedge clk_por or negedge ${info_rst}) begin
    if (!${info_rst}) begin
      cpu_info_en_q  <= 1'b0;
      cpu_info_idx_q <= '0;
    end else begin
      if (intraip_p2s_i.cpu_info_en_set) begin
        cpu_info_en_q <= 1'b1;
      end else if (intraip_p2s_i.cpu_info_en_clr || rst_hw_req) begin
        cpu_info_en_q <= 1'b0;
      end
      if (intraip_p2s_i.cpu_info_idx_we) begin
        cpu_info_idx_q <= intraip_p2s_i.cpu_info_idx_wd;
      end
    end
  end

  assign intraip_s2p_o.cpu_info_en_q    = cpu_info_en_q;
  assign intraip_s2p_o.cpu_info_idx_q   = cpu_info_idx_q;
  assign intraip_s2p_o.cpu_dump_capture = (rst_hw_req | rst_low_power) & cpu_info_en_q;

  // ERR_CODE: the record of the errors, one bit per field:
  //  - REG_INTG_ERR: the integrity error of the register file.
  //  - RESET_CONSISTENCY_ERR: the consistency errors of the leaves of both partitions.
  //  - FSM_ERR: the FSM errors of the leaves of both partitions.
  // Keeping the record here, in the always-on power domain, keeps it through a deep sleep cycle,
  // and captures tampering with the Aon resets, under these requirements:
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

  always_ff @(posedge intraip_p2s_i.clk or negedge reg_rst_n) begin
    if (!reg_rst_n) begin
      reg_intg_err_q  <= 1'b0;
      cnsty_chk_err_q <= 1'b0;
      fsm_err_q       <= 1'b0;
    end else begin
      reg_intg_err_q  <= reg_intg_err_q || intraip_p2s_i.reg_intg_err;
      cnsty_chk_err_q <= cnsty_chk_err_q || cnsty_chk_err;
      fsm_err_q       <= fsm_err_q || fsm_err;
    end
  end

  assign intraip_s2p_o.reg_intg_err_q  = reg_intg_err_q;
  assign intraip_s2p_o.cnsty_chk_err_q = cnsty_chk_err_q;
  assign intraip_s2p_o.fsm_err_q       = fsm_err_q;

  `ASSERT(RegIntgErrRecordSticky_A, reg_intg_err_q |=> reg_intg_err_q, intraip_p2s_i.clk,
          !reg_rst_n)
  `ASSERT(CnstyChkErrRecordSticky_A, cnsty_chk_err_q |=> cnsty_chk_err_q, intraip_p2s_i.clk,
          !reg_rst_n)
  `ASSERT(FsmErrRecordSticky_A, fsm_err_q |=> fsm_err_q, intraip_p2s_i.clk,
          !reg_rst_n)

  // rst_aon_ni completes the partition's primary clocking pair, and is not used.
  logic unused_rst_aon;
  assign unused_rst_aon = rst_aon_ni;
% if not n_err:
  // Without leaves, this partition does not use the parameters of the leaves, or the clocks that
  // only leaves use.
  logic unused_leaf_cfg;
  assign unused_leaf_cfg = ^{SecCheck, SecMaxSyncDelay${''.join(f", intraip_p2s_i.clk_{c}" for c in secondary_clk_names if c != 'aon')}};
% endif

<%
  ## The resets that this partition outputs but the other partition produces, and the resets that it
  ## produces for the other partition to output. A top may have neither.
  route_lines = []
  for rst in output_rsts:
    names = [rst['name']] + ([rst['name'] + '_shadowed'] if rst['shadowed'] else [])
    prod_doms = rstmgr_hosted_domains(rst, 'secondary')
    for n in names:
      # Each copy has its own output domains, because the shadowed copy goes only where a module
      # uses it.
      out_doms = rstmgr_out_domains(rst, 'secondary', n)
      other_out = rstmgr_out_domains(rst, 'primary', n)
      out_arr = bool(out_doms) and rstmgr_is_array(out_doms, power_domains)
      for d in out_doms:
        if d not in prod_doms:
          osel = f"[Domain{d}Sel]" if out_arr else ""
          lhs = f"resets_secondary_o.rst_{n}_n{osel}"
          rhs = f"intraip_p2s_i.rst_{n}_n_{d.lower()}"
          line = f"  assign {lhs} = {rhs};"
          route_lines.append(line if len(line) <= 100 else f"  assign {lhs} =\n      {rhs};")
      for d in prod_doms:
        if d in other_out:
          route_lines.append(
              f"  assign intraip_s2p_o.rst_{n}_n_{d.lower()} = {leaf_dst(rst, n, d)};")
%>\
% if route_lines:
  ////////////////////////////////////////////////////
  // Routing. This partition outputs the resets of the modules of the always-on power domain.
  ////////////////////////////////////////////////////
% for line in route_lines:
${line}
% endfor
% endif

  // The reset asserted indications that this partition generates go to the primary partition, which
  // outputs them. Each leaf drives its field of intraip_s2p_o directly.

  ////////////////////////////////////////////////////
  // Assertions                                     //
  ////////////////////////////////////////////////////
  `ASSERT_KNOWN(PwrKnownO_A,     pwr_o,              intraip_p2s_i.clk, !reg_rst_n)
  `ASSERT_KNOWN(ResetsKnownO_A,  resets_secondary_o, intraip_p2s_i.clk, !reg_rst_n)
  `ASSERT_KNOWN(IntraipKnownO_A, intraip_s2p_o,      intraip_p2s_i.clk, !reg_rst_n)
endmodule // rstmgr_part_secondary
