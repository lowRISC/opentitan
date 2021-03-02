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

  // Power domain parameters
  parameter int PowerDomains = 2;
  parameter int DomainAonSel = 0;
  parameter int Domain0Sel = 1;

  // Number of non-always-on domains
  parameter int OffDomains = PowerDomains-1;

  // positions of software controllable reset bits
  parameter int SPI_DEVICE = 0;
  parameter int SPI_HOST0 = 1;
  parameter int SPI_HOST1 = 2;
  parameter int USB = 3;
  parameter int I2C0 = 4;
  parameter int I2C1 = 5;
  parameter int I2C2 = 6;

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
    logic [PowerDomains-1:0] rst_sys_io_div4_n;
    logic [PowerDomains-1:0] rst_sys_aon_n;
    logic [PowerDomains-1:0] rst_spi_device_n;
    logic [PowerDomains-1:0] rst_spi_host0_n;
    logic [PowerDomains-1:0] rst_spi_host1_n;
    logic [PowerDomains-1:0] rst_usb_n;
    logic [PowerDomains-1:0] rst_i2c0_n;
    logic [PowerDomains-1:0] rst_i2c1_n;
    logic [PowerDomains-1:0] rst_i2c2_n;
  } rstmgr_out_t;

  // cpu reset requests and status
  typedef struct packed {
    logic rst_cpu_n;
    logic ndmreset_req;
  } rstmgr_cpu_t;

  // exported resets
  typedef struct packed {
    logic [PowerDomains-1:0] rst_ast_usbdev_sys_io_div4_n;
    logic [PowerDomains-1:0] rst_ast_usbdev_sys_aon_n;
    logic [PowerDomains-1:0] rst_ast_usbdev_usb_n;
    logic [PowerDomains-1:0] rst_ast_ast_sys_io_div4_n;
    logic [PowerDomains-1:0] rst_ast_sensor_ctrl_aon_sys_io_div4_n;
    logic [PowerDomains-1:0] rst_ast_entropy_src_sys_n;
    logic [PowerDomains-1:0] rst_ast_edn0_sys_n;
  } rstmgr_ast_out_t;

  // default value for rstmgr_ast_rsp_t (for dangling ports)
  parameter rstmgr_cpu_t RSTMGR_CPU_DEFAULT = '{
    rst_cpu_n: 1'b1,
    ndmreset_req: '0
  };

endpackage // rstmgr_pkg
