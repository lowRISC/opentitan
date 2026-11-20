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
  parameter int SPI_HOST1 = 2;
  parameter int USB = 3;
  parameter int USB_AON = 4;
  parameter int I2C0 = 5;
  parameter int I2C1 = 6;
  parameter int I2C2 = 7;
  parameter int I3C0 = 8;
  parameter int I3C1 = 9;

  // Resets generated and broadcast. The primary partition outputs the resets of the power domain
  // that powers down. The secondary partition outputs the resets of the always-on power domain. A
  // reset that a partition outputs for every power domain is an array over the domains. A reset
  // that it outputs for a single power domain is a single bit.
  // SEC_CM: LEAF.RST.SHADOW
  typedef struct packed {
    logic [PowerDomains-1:0] rst_por_aon_n;
    logic rst_por_io_div4_n;
    logic rst_lc_aon_n;
    logic rst_lc_io_div4_shadowed_n;
    logic [PowerDomains-1:0] rst_lc_io_div4_n;
    logic rst_sys_io_div4_n;
  } rstmgr_out_secondary_t;

  // SEC_CM: LEAF.RST.SHADOW
  typedef struct packed {
    logic rst_por_n;
    logic rst_por_io_n;
    logic rst_por_io_div4_n;
    logic rst_por_usb_n;
    logic rst_lc_shadowed_n;
    logic rst_lc_n;
    logic rst_lc_aon_n;
    logic rst_lc_io_n;
    logic rst_lc_io_div4_shadowed_n;
    logic rst_lc_io_div4_n;
    logic rst_lc_usb_n;
    logic rst_sys_n;
    logic rst_spi_device_n;
    logic rst_spi_host0_n;
    logic rst_spi_host1_n;
    logic rst_usb_n;
    logic rst_usb_aon_n;
    logic rst_i2c0_n;
    logic rst_i2c1_n;
    logic rst_i2c2_n;
    logic rst_i3c0_n;
    logic rst_i3c1_n;
  } rstmgr_out_primary_t;

  // Reset asserted indications for the alert handlers. The primary partition outputs all of them.
  // The secondary partition's indications cross to it in intraip_s2p.
  typedef struct packed {
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por_aon;
    prim_mubi_pkg::mubi4_t por;
    prim_mubi_pkg::mubi4_t por_io;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por_io_div4;
    prim_mubi_pkg::mubi4_t por_usb;
    prim_mubi_pkg::mubi4_t lc_shadowed;
    prim_mubi_pkg::mubi4_t lc;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] lc_aon;
    prim_mubi_pkg::mubi4_t lc_io;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] lc_io_div4_shadowed;
    prim_mubi_pkg::mubi4_t [PowerDomains-1:0] lc_io_div4;
    prim_mubi_pkg::mubi4_t lc_usb;
    prim_mubi_pkg::mubi4_t sys;
    prim_mubi_pkg::mubi4_t sys_io_div4;
    prim_mubi_pkg::mubi4_t spi_device;
    prim_mubi_pkg::mubi4_t spi_host0;
    prim_mubi_pkg::mubi4_t spi_host1;
    prim_mubi_pkg::mubi4_t usb;
    prim_mubi_pkg::mubi4_t usb_aon;
    prim_mubi_pkg::mubi4_t i2c0;
    prim_mubi_pkg::mubi4_t i2c1;
    prim_mubi_pkg::mubi4_t i2c2;
    prim_mubi_pkg::mubi4_t i3c0;
    prim_mubi_pkg::mubi4_t i3c1;
  } rstmgr_rst_en_primary_t;

  parameter int NumOutputRst = 24 * PowerDomains;

  // Signalling between the two partitions of the split reset manager.
  // Secondary (reset roots, always-on side) to primary
  typedef struct packed {
    // The reset roots, per power domain, that the primary partition's leaf resets have as parents.
    logic rst_por_aon_n_main;
    logic rst_lc_src_n_main;
    logic rst_sys_src_n_main;
    // The scan signals, which enter this partition only.
    prim_mubi_pkg::mubi4_t scanmode;
    logic scan_rst_n;
    // The registers that this partition keeps in the always-on power domain, in the order of the
    // address map, which the primary partition reads:
    //  - reset_req_q: the software reset request of RESET_REQ.
    //  - reset_info_q: the reset reasons of RESET_INFO.
    //  - *_regwen_q: the locks ALERT_REGWEN and CPU_REGWEN.
    //  - *_info_en_q, *_info_idx_q: the EN and INDEX fields of ALERT_INFO_CTRL and CPU_INFO_CTRL.
    // With them, the captures of the alert and CPU dumps, which the primary partition stores: a
    // hardware reset or a low power entry while the dump is enabled.
    prim_mubi_pkg::mubi4_t reset_req_q;
    rstmgr_reg_pkg::rstmgr_hw2reg_reset_info_reg_t reset_info_q;
    logic alert_regwen_q;
    logic alert_info_en_q;
    logic [rstmgr_reg_pkg::IdxWidth-1:0] alert_info_idx_q;
    logic alert_dump_capture;
    logic cpu_regwen_q;
    logic cpu_info_en_q;
    logic [rstmgr_reg_pkg::IdxWidth-1:0] cpu_info_idx_q;
    logic cpu_dump_capture;
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
    prim_mubi_pkg::mubi4_t rst_en_por_aon_main;
    prim_mubi_pkg::mubi4_t rst_en_por_aon_aon;
    prim_mubi_pkg::mubi4_t rst_en_por_io_div4_aon;
    prim_mubi_pkg::mubi4_t rst_en_lc_aon_aon;
    prim_mubi_pkg::mubi4_t rst_en_lc_io_div4_aon;
    prim_mubi_pkg::mubi4_t rst_en_lc_io_div4_shadowed_aon;
    prim_mubi_pkg::mubi4_t rst_en_sys_io_div4_aon;
  } intraip_s2p_t;

  // Primary to secondary
  typedef struct packed {
    // The clocks that the secondary partition uses. Only the primary partition receives them.
    //  - clk: the bus clock, for the consistency checks of the leaf resets and the record of
    //    ERR_CODE.
    //  - clk_por: the POR clock, for the reset controllers and RESET_INFO.
    //  - The clocks of some leaf resets.
    logic clk;
    logic clk_por;
    logic clk_io_div4;
    // The software writes to the registers that the secondary partition keeps, in the order of the
    // address map. The clamp of a power domain that powers down holds each at 0, which writes
    // nothing:
    //  - reset_req_we, reset_req_wd: a write to RESET_REQ. With the write enable at 0, nothing is
    //    written.
    //  - *_clr of RESET_INFO: one bit per bit of the register. A 1 clears that reason (rw1c).
    //  - *_regwen_clr: a write of 0 to ALERT_REGWEN or CPU_REGWEN, which clears it (rw0c).
    //  - *_info_en_set, *_info_en_clr: a write of 1 or of 0 to the EN field of ALERT_INFO_CTRL or
    //    CPU_INFO_CTRL.
    //  - *_info_idx_we, *_info_idx_wd: a write to the INDEX field of the same register. With the
    //    write enable at 0, nothing is written.
    logic reset_req_we;
    prim_mubi_pkg::mubi4_t reset_req_wd;
    logic por_clr;
    logic low_power_exit_clr;
    logic sw_reset_clr;
    logic [rstmgr_reg_pkg::NumHwResets-1:0] hw_req_clr;
    logic alert_regwen_clr;
    logic alert_info_en_set;
    logic alert_info_en_clr;
    logic alert_info_idx_we;
    logic [rstmgr_reg_pkg::IdxWidth-1:0] alert_info_idx_wd;
    logic cpu_regwen_clr;
    logic cpu_info_en_set;
    logic cpu_info_en_clr;
    logic cpu_info_idx_we;
    logic [rstmgr_reg_pkg::IdxWidth-1:0] cpu_info_idx_wd;
    // The errors of this partition, for the record of ERR_CODE in the secondary partition. They are
    // the integrity error of the register file, and the aggregated consistency and FSM errors of
    // the leaf resets that this partition hosts.
    logic reg_intg_err;
    logic cnsty_chk_err;
    logic fsm_err;
    // The resets that the primary partition generates and that modules in the power domain of the
    // secondary partition use.
    logic rst_lc_io_div4_n_main;
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
