// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module is the overall reset manager wrapper
// TODO: This module is only a draft implementation that covers most of the rstmgr
// functoinality but is incomplete

package rstmgr_pkg;

  // global constants
  parameter int ALWAYS_ON_SEL    = pwrmgr_pkg::ALWAYS_ON_DOMAIN;

  // params that reference pwrmgr, should be replaced once pwrmgr is merged
  parameter int PowerDomains    = pwrmgr_pkg::PowerDomains;
  parameter int ExtResetReasons = pwrmgr_pkg::HwRstReqs;

  // calculated domains
  parameter int OffDomains = PowerDomains-1;

  // low power exit + external reasons + ndm_reset_req
  parameter int ResetReasons = 1 + ExtResetReasons + 1;

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
    logic rst_por_aon_n;
    logic rst_por_n;
    logic rst_por_io_n;
    logic rst_por_io_div2_n;
    logic rst_por_usb_n;
    logic rst_lc_n;
    logic rst_sys_n;
    logic rst_sys_io_n;
    logic rst_sys_aon_n;
    logic rst_spi_device_n;
    logic rst_usb_n;
  } rstmgr_out_t;

  // cpu reset requests and status
  typedef struct packed {
    logic rst_cpu_n;
    logic ndmreset_req;
  } rstmgr_cpu_t;

  // default value for rstmgr_ast_rsp_t (for dangling ports)
  parameter rstmgr_cpu_t RSTMGR_CPU_DEFAULT = '{
    rst_cpu_n: 1'b1,
    ndmreset_req: '0
  };

  // peripherals reset requests
  typedef struct packed {
    logic [ExtResetReasons-1:0] rst_reqs;
  } rstmgr_peri_t;

  // default value for rstmgr_ast_rsp_t (for dangling ports)
  parameter rstmgr_peri_t RSTMGR_PERI_DEFAULT = '{
    rst_reqs: '0
  };


endpackage // rstmgr_pkg
