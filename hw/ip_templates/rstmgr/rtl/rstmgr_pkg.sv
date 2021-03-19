// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module is the overall reset manager wrapper
// TODO: This module is only a draft implementation that covers most of the rstmgr
// functoinality but is incomplete

package rstmgr_pkg;

  // Power domain parameters
  parameter int PowerDomains = 2;
  parameter int DomainAonSel = 0;
  parameter int Domain0Sel = 1;

  // Number of non-always-on domains
  parameter int OffDomains = PowerDomains - 1;

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
    logic [PowerDomains-1:0] rst_por_aon_n;
    logic [PowerDomains-1:0] rst_por_n;
    logic [PowerDomains-1:0] rst_por_io_n;
    logic [PowerDomains-1:0] rst_por_io_div2_n;
    logic [PowerDomains-1:0] rst_por_io_div4_n;
    logic [PowerDomains-1:0] rst_por_usb_n;
    logic [PowerDomains-1:0] rst_lc_n;
    logic [PowerDomains-1:0] rst_lc_io_div4_n;
    logic [PowerDomains-1:0] rst_sys_n;
    logic [PowerDomains-1:0] rst_sys_io_n;
    logic [PowerDomains-1:0] rst_sys_io_div4_n;
    logic [PowerDomains-1:0] rst_sys_aon_n;
    logic [PowerDomains-1:0] rst_spi_device_n;
    logic [PowerDomains-1:0] rst_usb_n;
  } rstmgr_out_t;

  // cpu reset requests and status
  typedef struct packed {
    logic rst_cpu_n;
    logic ndmreset_req;
  } rstmgr_cpu_t;

  // exported resets
  typedef struct packed {
    logic [PowerDomains-1:0] rst_ast_usbdev_sys_io_div4_n;
    logic [PowerDomains-1:0] rst_ast_usbdev_usb_n;
    logic [PowerDomains-1:0] rst_ast_sensor_ctrl_sys_io_div4_n;
  } rstmgr_ast_out_t;

  // default value for rstmgr_ast_rsp_t (for dangling ports)
  parameter rstmgr_cpu_t RSTMGR_CPU_DEFAULT = '{
    rst_cpu_n: 1'b1,
    ndmreset_req: '0
  };

endpackage // rstmgr_pkg
