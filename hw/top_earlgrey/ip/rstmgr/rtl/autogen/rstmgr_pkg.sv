// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
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
  parameter int SPI_DEVICE = 0;
  parameter int USB = 1;

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
    logic rst_por_io_div4_n;
    logic rst_por_usb_n;
    logic rst_lc_n;
    logic rst_lc_io_n;
    logic rst_sys_n;
    logic rst_sys_io_n;
    logic rst_sys_io_div4_n;
    logic rst_sys_aon_n;
    logic rst_spi_device_n;
    logic rst_usb_n;
  } rstmgr_out_t;

  // cpu reset requests and status
  typedef struct packed {
    logic rst_cpu_n;
    logic ndmreset_req;
  } rstmgr_cpu_t;

  // exported resets
  typedef struct packed {
    logic rst_ast_usbdev_sys_io_div4_n;
    logic rst_ast_usbdev_usb_n;
    logic rst_ast_sensor_ctrl_sys_io_div4_n;
  } rstmgr_ast_out_t;

  // default value for rstmgr_ast_rsp_t (for dangling ports)
  parameter rstmgr_cpu_t RSTMGR_CPU_DEFAULT = '{
    rst_cpu_n: 1'b1,
    ndmreset_req: '0
  };

endpackage // rstmgr_pkg
