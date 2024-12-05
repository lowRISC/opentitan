// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

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
  parameter int I2C0 = 2;

  // resets generated and broadcast
  // SEC_CM: LEAF.RST.SHADOW
  typedef struct packed {
    logic [PowerDomains-1:0] rst_por_aon_n;
    logic [PowerDomains-1:0] rst_por_n;
    logic [PowerDomains-1:0] rst_por_io_n;
    logic [PowerDomains-1:0] rst_por_io_div2_n;
    logic [PowerDomains-1:0] rst_por_io_div4_n;
    logic [PowerDomains-1:0] rst_por_usb_n;
    logic [PowerDomains-1:0] rst_lc_shadowed_n;
    logic [PowerDomains-1:0] rst_lc_n;
    logic [PowerDomains-1:0] rst_lc_aon_n;
    logic [PowerDomains-1:0] rst_lc_io_n;
    logic [PowerDomains-1:0] rst_lc_io_div2_n;
    logic [PowerDomains-1:0] rst_lc_io_div4_shadowed_n;
    logic [PowerDomains-1:0] rst_lc_io_div4_n;
    logic [PowerDomains-1:0] rst_lc_usb_n;
    logic [PowerDomains-1:0] rst_sys_n;
    logic [PowerDomains-1:0] rst_sys_io_div4_n;
    logic [PowerDomains-1:0] rst_spi_device_n;
    logic [PowerDomains-1:0] rst_spi_host0_n;
    logic [PowerDomains-1:0] rst_i2c0_n;
  } rstmgr_out_t;

  // reset indication for alert handler
  typedef struct packed {
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por_aon;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por_io;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por_io_div2;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por_io_div4;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por_usb;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] lc_shadowed;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] lc;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] lc_aon;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] lc_io;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] lc_io_div2;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] lc_io_div4_shadowed;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] lc_io_div4;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] lc_usb;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] sys;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] sys_io_div4;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] spi_device;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] spi_host0;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] i2c0;
  } rstmgr_rst_en_t;

  parameter int NumOutputRst = 19 * PowerDomains;

  // cpu reset requests and status
  typedef struct packed {
    logic ndmreset_req;
  } rstmgr_cpu_t;

  // exported resets

  // default value for rstmgr_ast_rsp_t (for dangling ports)
  parameter rstmgr_cpu_t RSTMGR_CPU_DEFAULT = '{
    ndmreset_req: '0
  };

  // Enumeration for pwrmgr hw reset inputs
  localparam int ResetWidths = $clog2(rstmgr_reg_pkg::NumTotalResets);
  typedef enum logic [ResetWidths-1:0] {
    ReqPeriResetIdx[0:1],
    ReqMainPwrResetIdx,
    ReqEscResetIdx,
    ReqNdmResetIdx
  } reset_req_idx_e;

  // Enumeration for reset info bit idx
  typedef enum logic [ResetWidths-1:0] {
    InfoPorIdx,
    InfoLowPowerExitIdx,
    InfoSwResetIdx,
    InfoPeriResetIdx[0:1],
    InfoMainPwrResetIdx,
    InfoEscResetIdx,
    InfoNdmResetIdx
  } reset_info_idx_e;


endpackage // rstmgr_pkg
