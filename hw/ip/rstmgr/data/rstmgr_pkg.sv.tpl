// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module is the overall reset manager wrapper
// TODO: This module is only a draft implementation that covers most of the rstmgr
// functoinality but is incomplete

package rstmgr_pkg;

  // global constants
  parameter int ALWAYS_ON_SEL   = pwrmgr_pkg::ALWAYS_ON_DOMAIN;

  // params that reference pwrmgr, should be replaced once pwrmgr is merged
  parameter int PowerDomains  = pwrmgr_pkg::PowerDomains;
  //parameter int HwResetReqs   = pwrmgr_pkg::NumRstReqs;

  // calculated domains
  parameter int OffDomains = PowerDomains-1;

  // positions of software controllable reset bits
% for rst in sw_rsts:
  parameter int ${rst['name'].upper()} = ${loop.index};
% endfor

  // ast interface
  typedef struct packed {
    logic aon_pok;
  } rstmgr_ast_t;

  // default value for rstmgr_ast_rsp_t (for dangling ports)
  parameter rstmgr_ast_t RSTMGR_AST_DEFAULT = '{
    aon_pok: 1'b1
  };

  // resets generated and broadcast
  // This should be templatized and generated
  typedef struct packed {
% for rst in output_rsts:
    logic rst_${rst['name']}_n;
% endfor
  } rstmgr_out_t;

  // cpu reset requests and status
  typedef struct packed {
    logic rst_cpu_n;
    logic ndmreset_req;
  } rstmgr_cpu_t;

  // exported resets
% for intf, eps in export_rsts.items():
  typedef struct packed {
  % for ep, rsts in eps.items():
    % for rst in rsts:
    logic rst_${intf}_${ep}_${rst}_n;
    % endfor
  % endfor
  } rstmgr_${intf}_out_t;
% endfor

  // default value for rstmgr_ast_rsp_t (for dangling ports)
  parameter rstmgr_cpu_t RSTMGR_CPU_DEFAULT = '{
    rst_cpu_n: 1'b1,
    ndmreset_req: '0
  };

endpackage // rstmgr_pkg
