// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
<%
  peri_reqs = reqs.get("peripheral", [])
  int_reqs = reqs.get("int", [])
  debug_reqs = reqs.get("debug", [])
  from ipgen.manager_split import (rstmgr_clocks, rstmgr_hosted_domains, rstmgr_is_array,
                                   rstmgr_out_domains, rstmgr_routed_rsts, rstmgr_rst_en_routed,
                                   rstmgr_routed_roots)
  # A reset, or the shadowed copy of a reset, crosses to the other partition only if a module in
  # that partition's power domain uses it. It crosses once, as a single bit.
  def routed_rsts(to_part):
    return rstmgr_routed_rsts(output_rsts, to_part)
  split_clks = rstmgr_clocks(clk_freqs, leaf_rsts, rst_ni)
  n_rst = sum(2 if r['shadowed'] else 1 for r in output_rsts)
%>\

package rstmgr_pkg;

  // Power domain parameters
  parameter int PowerDomains = ${len(power_domains)};
  % for power_domain in power_domains:
  parameter int Domain${power_domain}Sel = ${loop.index};
  % endfor

  // Number of non-always-on domains
  parameter int OffDomains = PowerDomains-1;

  // positions of software controllable reset bits
% for device in sw_rsts.keys():
  parameter int ${device.upper()} = ${loop.index};
% endfor

  // Resets generated and broadcast. The primary partition outputs the resets of the power domain
  // that powers down. The secondary partition outputs the resets of the always-on power domain. A
  // reset that a partition outputs for every power domain is an array over the domains. A reset
  // that it outputs for a single power domain is a single bit.
% for part in ('secondary', 'primary'):
  // SEC_CM: LEAF.RST.SHADOW
  typedef struct packed {
  % for rst in output_rsts:
<% outs = rstmgr_out_domains(rst, part)
arr = '[PowerDomains-1:0] ' if outs and rstmgr_is_array(outs, power_domains) else ''
souts = rstmgr_out_domains(rst, part, rst['name'] + '_shadowed') if rst['shadowed'] else []
sarr = '[PowerDomains-1:0] ' if souts and rstmgr_is_array(souts, power_domains) else '' %>\
    % if souts:
    logic ${sarr}rst_${rst['name']}_shadowed_n;
    % endif
    % if outs:
    logic ${arr}rst_${rst['name']}_n;
    % endif
  % endfor
  } rstmgr_out_${part}_t;

% endfor
  // Reset asserted indications for the alert handlers. The primary partition outputs all of them.
  // The secondary partition's indications cross to it in intraip_s2p.
  typedef struct packed {
% for rst in output_rsts:
<% arr = '[PowerDomains-1:0] ' if rstmgr_is_array(rst['domains'], power_domains) else '' %>\
  % if rst['shadowed']:
    prim_mubi_pkg::mubi4_t ${arr}${rst['name']}_shadowed;
  % endif
    prim_mubi_pkg::mubi4_t ${arr}${rst['name']};
% endfor
  } rstmgr_rst_en_primary_t;

  parameter int NumOutputRst = ${n_rst} * PowerDomains;

  // Signalling between the two partitions of the split reset manager.
  // Secondary (reset roots, always-on side) to primary
  typedef struct packed {
    // The reset roots, per power domain, that the primary partition's leaf resets have as parents.
% for root, domain in rstmgr_routed_roots(leaf_rsts):
    logic rst_${root}_n_${domain.lower()};
% endfor
    // The parts of the power manager's reset request that the primary partition reads. They are the
    // lc and sys requests and the reset cause. The hardware reset requests stay in this partition,
    // for RESET_INFO.
    logic [PowerDomains-1:0] pwr_rst_lc_req;
    logic [PowerDomains-1:0] pwr_rst_sys_req;
    pwrmgr_pkg::reset_cause_e pwr_reset_cause;
    // The scan signals, which enter this partition only.
    prim_mubi_pkg::mubi4_t scanmode;
    logic scan_rst_n;
    // The reset reasons of RESET_INFO, which this partition keeps in the always-on power domain.
    rstmgr_reg_pkg::rstmgr_hw2reg_reset_info_reg_t reset_info;
    // The record of the errors of ERR_CODE, which this partition keeps in the always-on power
    // domain. It holds the integrity error of the register file of the primary partition, and the
    // consistency and FSM errors of the leaf resets of both partitions. The names end in _q, after
    // the sticky flops that hold them, to tell them from the errors that the primary partition
    // detects (intraip_p2s).
    logic reg_intg_err_q;
    logic cnsty_chk_err_q;
    logic fsm_err_q;
    // The resets that the secondary partition generates and that modules in the power domain of the
    // primary partition use.
% for r in routed_rsts('primary'):
    logic ${r};
% endfor
    // The reset asserted indications that the secondary partition generates. The primary partition
    // outputs them.
% for f, _, _ in rstmgr_rst_en_routed(output_rsts):
    prim_mubi_pkg::mubi4_t ${f};
% endfor
  } intraip_s2p_t;

  // Primary to secondary
  typedef struct packed {
    // The errors of this partition, for the record in the secondary partition. They are the
    // integrity error of the register file, and the aggregated consistency and FSM errors of the
    // leaf resets that this partition hosts.
    logic reg_intg_err;
    logic cnsty_chk_err;
    logic fsm_err;
    // The clocks that the secondary partition uses. Only the primary partition receives them.
    //  - clk: the bus clock, for the consistency checks of the leaf resets and the record of
    //    ERR_CODE.
    //  - clk_por: the POR clock, for the reset controllers and RESET_INFO.
    //  - The clocks of some leaf resets.
    logic clk;
    logic clk_por;
% for clk in split_clks.forwarded['secondary']:
    logic clk_${clk};
% endfor
    // The software writes to RESET_INFO, which the secondary partition keeps, and the software
    // reset request that its SW_RESET field records.
    rstmgr_reg_pkg::rstmgr_reg2hw_reset_info_reg_t reset_info;
    prim_mubi_pkg::mubi4_t sw_rst_req;
% if routed_rsts('secondary'):
    // The resets that the primary partition generates and that modules in the power domain of the
    // secondary partition use.
  % for r in routed_rsts('secondary'):
    logic ${r};
  % endfor
% endif
  } intraip_p2s_t;

  // cpu reset requests and status
  typedef struct packed {
    logic ndmreset_req;
  } rstmgr_cpu_t;

  // exported resets
% for intf, eps in export_rsts.items():
  typedef struct packed {
  % for ep, rsts in eps.items():
    % for rst in rsts:
    logic [PowerDomains-1:0] rst_${intf}_${ep}_${rst['name']}_n;
    % endfor
  % endfor
  } rstmgr_${intf}_out_t;
% endfor

  // default value for rstmgr_ast_rsp_t (for dangling ports)
  parameter rstmgr_cpu_t RSTMGR_CPU_DEFAULT = '{
    ndmreset_req: '0
  };

  // Enumeration for pwrmgr hw reset inputs
  import rstmgr_reg_pkg::NumTotalResets;
  localparam int ResetWidths = $clog2(NumTotalResets);
  typedef enum logic [ResetWidths-1:0] {
    ReqPeriResetIdx[0:${len(peri_reqs)-1}],
    % for req in (int_reqs + debug_reqs):
    ${f"Req{req['name']}ResetIdx"}${"" if loop.last else ","}
    % endfor
  } reset_req_idx_e;

  // Enumeration for reset info bit idx
  typedef enum logic [ResetWidths-1:0] {
    InfoPorIdx,
    InfoLowPowerExitIdx,
    InfoSwResetIdx,
    InfoPeriResetIdx[0:${len(peri_reqs)-1}],
    % for req in (int_reqs + debug_reqs):
    ${f"Info{req['name']}ResetIdx"}${"" if loop.last else ","}
    % endfor
  } reset_info_idx_e;


endpackage // rstmgr_pkg
