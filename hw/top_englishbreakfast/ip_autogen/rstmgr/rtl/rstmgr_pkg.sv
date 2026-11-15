// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package rstmgr_pkg;

  // Power domain parameters
  parameter int PowerDomains = 2;
  parameter int DomainAonSel = 0;
  parameter int DomainMainSel = 1;

  // Number of non-always-on domains
  parameter int OffDomains = PowerDomains-1;

  // positions of software controllable reset bits
  parameter int SPI_DEVICE = 0;
  parameter int SPI_HOST0 = 1;
  parameter int USB = 2;

  // Resets generated and broadcast. The primary partition outputs the resets of the power domain
  // that powers down. The secondary partition outputs the resets of the always-on power domain. A
  // reset that a partition outputs for every power domain is an array over the domains. A reset
  // that it outputs for a single power domain is a single bit.
  // SEC_CM: LEAF.RST.SHADOW
  typedef struct packed {
    logic [PowerDomains-1:0] rst_por_aon_n;
    logic rst_por_io_div4_shadowed_n;
    logic rst_por_io_div4_n;
    logic rst_lc_io_div4_n;
    logic rst_sys_io_div4_n;
    logic rst_sys_aon_n;
  } rstmgr_out_secondary_t;

  // SEC_CM: LEAF.RST.SHADOW
  typedef struct packed {
    logic rst_por_n;
    logic rst_por_io_n;
    logic rst_por_io_div4_shadowed_n;
    logic rst_por_io_div4_n;
    logic rst_por_usb_n;
    logic rst_lc_shadowed_n;
    logic rst_lc_n;
    logic rst_lc_io_div4_n;
    logic rst_sys_shadowed_n;
    logic rst_sys_n;
    logic rst_sys_io_div4_n;
    logic rst_sys_aon_n;
    logic rst_spi_device_n;
    logic rst_spi_host0_n;
    logic rst_usb_n;
  } rstmgr_out_primary_t;

  // Reset asserted indications for the alert handlers. The primary partition outputs all of them.
  // The secondary partition's indications cross to it in intraip_s2p.
  typedef struct packed {
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por_aon;
    prim_mubi_pkg::mubi4_t por;
    prim_mubi_pkg::mubi4_t por_io;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por_io_div4_shadowed;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por_io_div4;
    prim_mubi_pkg::mubi4_t por_usb;
    prim_mubi_pkg::mubi4_t lc_shadowed;
    prim_mubi_pkg::mubi4_t lc;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] lc_io_div4;
    prim_mubi_pkg::mubi4_t sys_shadowed;
    prim_mubi_pkg::mubi4_t sys;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] sys_io_div4;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] sys_aon;
    prim_mubi_pkg::mubi4_t spi_device;
    prim_mubi_pkg::mubi4_t spi_host0;
    prim_mubi_pkg::mubi4_t usb;
  } rstmgr_rst_en_primary_t;

  parameter int NumOutputRst = 16 * PowerDomains;

  // Signalling between the two partitions of the split reset manager.
  // Secondary (reset roots, always-on side) to primary
  typedef struct packed {
    // The reset roots, per power domain, that the primary partition's leaf resets have as parents.
    logic rst_por_aon_n_main;
    logic rst_lc_src_n_main;
    logic rst_sys_src_n_main;
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
    // The reset asserted indications that the secondary partition generates. The primary partition
    // outputs them.
    prim_mubi_pkg::mubi4_t rst_en_por_aon_aon;
    prim_mubi_pkg::mubi4_t rst_en_por_aon_main;
    prim_mubi_pkg::mubi4_t rst_en_por_io_div4_aon;
    prim_mubi_pkg::mubi4_t rst_en_por_io_div4_shadowed_aon;
    prim_mubi_pkg::mubi4_t rst_en_lc_io_div4_aon;
    prim_mubi_pkg::mubi4_t rst_en_sys_io_div4_aon;
    prim_mubi_pkg::mubi4_t rst_en_sys_aon_aon;
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
    logic clk_io_div4;
    // The software writes to RESET_INFO, which the secondary partition keeps, and the software
    // reset request that its SW_RESET field records.
    rstmgr_reg_pkg::rstmgr_reg2hw_reset_info_reg_t reset_info;
    prim_mubi_pkg::mubi4_t sw_rst_req;
  } intraip_p2s_t;

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
  import rstmgr_reg_pkg::NumTotalResets;
  localparam int ResetWidths = $clog2(NumTotalResets);
  typedef enum logic [ResetWidths-1:0] {
    ReqPeriResetIdx[0:0],
    ReqMainPwrResetIdx,
    ReqEscResetIdx,
    ReqNdmResetIdx
  } reset_req_idx_e;

  // Enumeration for reset info bit idx
  typedef enum logic [ResetWidths-1:0] {
    InfoPorIdx,
    InfoLowPowerExitIdx,
    InfoSwResetIdx,
    InfoPeriResetIdx[0:0],
    InfoMainPwrResetIdx,
    InfoEscResetIdx,
    InfoNdmResetIdx
  } reset_info_idx_e;


endpackage // rstmgr_pkg
