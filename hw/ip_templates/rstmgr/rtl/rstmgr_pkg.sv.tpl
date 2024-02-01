// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package rstmgr_pkg;

  // Power domain parameters
  parameter int PowerDomains = ${len(power_domains)};
  % for power_domain in power_domains:
  parameter int Domain${power_domain}Sel = ${loop.index};
  % endfor

  // Number of non-always-on domains
  parameter int OffDomains = PowerDomains-1;

  // positions of software controllable reset bits
% for rst in sw_rsts:
  parameter int ${rst.upper()} = ${loop.index};
% endfor

  // resets generated and broadcast
  // SEC_CM: LEAF.RST.SHADOW
  typedef struct packed {
% for rst in output_rsts:
  % if rst['shadowed']:
    logic [PowerDomains-1:0] rst_${rst['name']}_shadowed_n;
  % endif
    logic [PowerDomains-1:0] rst_${rst['name']}_n;
% endfor
  } rstmgr_out_t;

  // reset indication for alert handler
  typedef struct packed {
<% n_rst = 0 %>\
% for rst in output_rsts:
  % if rst['shadowed']:
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] ${rst['name']}_shadowed;<% n_rst += 1 %>
  % endif
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] ${rst['name']};<% n_rst += 1 %>
% endfor
  } rstmgr_rst_en_t;

  parameter int NumOutputRst = ${n_rst} * PowerDomains;

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
  localparam int ResetWidths = $clog2(rstmgr_reg_pkg::NumTotalResets);
  typedef enum logic [ResetWidths-1:0] {
    ReqPeriResetIdx[0:${len(reqs["peripheral"])-1}],
    % for req in (reqs["int"] + reqs["debug"]):
    ${f"Req{req['name']}ResetIdx"}${"" if loop.last else ","}
    % endfor
  } reset_req_idx_e;

  // Enumeration for reset info bit idx
  typedef enum logic [ResetWidths-1:0] {
    InfoPorIdx,
    InfoLowPowerExitIdx,
    InfoSwResetIdx,
    InfoPeriResetIdx[0:${len(reqs["peripheral"])-1}],
    % for req in (reqs["int"] + reqs["debug"]):
    ${f"Info{req['name']}ResetIdx"}${"" if loop.last else ","}
    % endfor
  } reset_info_idx_e;


endpackage // rstmgr_pkg
