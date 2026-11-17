// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// clkmgr interface.

interface rstmgr_if (
  input logic clk_aon,
  input logic clk,
  input logic rst_n
);

  import rstmgr_env_pkg::*;
  import rstmgr_pkg::PowerDomains;

  logic                              [PowerDomains-1:0] por_n;

  pwrmgr_pkg::pwr_rst_req_t                             pwr_i;
  pwrmgr_pkg::pwr_rst_rsp_t                             pwr_o;

  prim_mubi_pkg::mubi4_t                                sw_rst_req_o;

  // cpu related inputs
  rstmgr_pkg::rstmgr_cpu_t                              cpu_i;

  // Interface to alert handler
  alert_handler_pkg::alert_crashdump_t                          alert_dump_i;

  // Interface to cpu crash dump
  rv_core_ibex_pkg::cpu_crash_dump_t                    cpu_dump_i;

  // dft bypass
  logic                                                 scan_rst_ni;
  prim_mubi_pkg::mubi4_t                                scanmode_i;

`ifndef PATH_TO_SECONDARY
  // The secondary partition of the rstmgr.
  `define PATH_TO_SECONDARY tb.dut_secondary
`endif

  // The resets that the two partitions output, from the testbench.
  rstmgr_pkg::rstmgr_out_primary_t                      resets_primary;
  rstmgr_pkg::rstmgr_out_secondary_t                    resets_secondary;

  // Every reset of the reset manager, for every power domain, as the single power-domain reset
  // manager output them. Each reset comes from a partition that outputs it, the primary if both do.
  // A power domain that a reset does not have holds it in reset, except rst_por_aon_n. The
  // secondary partition generates rst_por_aon_n for every power domain, as the single power-domain
  // reset manager did, and outputs only the domains of the reset tree. So resets_o takes it whole
  // from the partition.
  typedef struct packed {
    logic [rstmgr_pkg::PowerDomains-1:0] rst_por_aon_n;
    logic [rstmgr_pkg::PowerDomains-1:0] rst_por_n;
    logic [rstmgr_pkg::PowerDomains-1:0] rst_por_io_n;
    logic [rstmgr_pkg::PowerDomains-1:0] rst_lc_shadowed_n;
    logic [rstmgr_pkg::PowerDomains-1:0] rst_lc_n;
    logic [rstmgr_pkg::PowerDomains-1:0] rst_lc_aon_n;
    logic [rstmgr_pkg::PowerDomains-1:0] rst_lc_io_shadowed_n;
    logic [rstmgr_pkg::PowerDomains-1:0] rst_lc_io_n;
    logic [rstmgr_pkg::PowerDomains-1:0] rst_sys_n;
    logic [rstmgr_pkg::PowerDomains-1:0] rst_spi_device_n;
    logic [rstmgr_pkg::PowerDomains-1:0] rst_spi_host0_n;
    logic [rstmgr_pkg::PowerDomains-1:0] rst_i2c0_n;
  } rstmgr_out_t;

  // reset outputs
  rstmgr_out_t                                          resets_o;

  assign resets_o.rst_por_n[rstmgr_pkg::DomainAonSel] = '0;
  assign resets_o.rst_por_n[rstmgr_pkg::DomainMainSel] =
      resets_primary.rst_por_n;
  assign resets_o.rst_por_io_n[rstmgr_pkg::DomainAonSel] =
      resets_secondary.rst_por_io_n;
  assign resets_o.rst_por_io_n[rstmgr_pkg::DomainMainSel] =
      resets_primary.rst_por_io_n;
  assign resets_o.rst_lc_n[rstmgr_pkg::DomainAonSel] = '0;
  assign resets_o.rst_lc_n[rstmgr_pkg::DomainMainSel] =
      resets_primary.rst_lc_n;
  assign resets_o.rst_lc_shadowed_n[rstmgr_pkg::DomainAonSel] = '0;
  assign resets_o.rst_lc_shadowed_n[rstmgr_pkg::DomainMainSel] =
      resets_primary.rst_lc_shadowed_n;
  assign resets_o.rst_lc_aon_n[rstmgr_pkg::DomainAonSel] =
      resets_secondary.rst_lc_aon_n;
  assign resets_o.rst_lc_aon_n[rstmgr_pkg::DomainMainSel] =
      resets_primary.rst_lc_aon_n;
  assign resets_o.rst_lc_io_n[rstmgr_pkg::DomainAonSel] =
      resets_secondary.rst_lc_io_n;
  assign resets_o.rst_lc_io_n[rstmgr_pkg::DomainMainSel] =
      resets_primary.rst_lc_io_n;
  assign resets_o.rst_lc_io_shadowed_n[rstmgr_pkg::DomainAonSel] =
      resets_secondary.rst_lc_io_shadowed_n;
  assign resets_o.rst_lc_io_shadowed_n[rstmgr_pkg::DomainMainSel] =
      resets_primary.rst_lc_io_shadowed_n;
  assign resets_o.rst_sys_n[rstmgr_pkg::DomainAonSel] = '0;
  assign resets_o.rst_sys_n[rstmgr_pkg::DomainMainSel] =
      resets_primary.rst_sys_n;
  assign resets_o.rst_spi_device_n[rstmgr_pkg::DomainAonSel] = '0;
  assign resets_o.rst_spi_device_n[rstmgr_pkg::DomainMainSel] =
      resets_primary.rst_spi_device_n;
  assign resets_o.rst_spi_host0_n[rstmgr_pkg::DomainAonSel] = '0;
  assign resets_o.rst_spi_host0_n[rstmgr_pkg::DomainMainSel] =
      resets_primary.rst_spi_host0_n;
  assign resets_o.rst_i2c0_n[rstmgr_pkg::DomainAonSel] = '0;
  assign resets_o.rst_i2c0_n[rstmgr_pkg::DomainMainSel] =
      resets_primary.rst_i2c0_n;
  assign resets_o.rst_por_aon_n = `PATH_TO_SECONDARY.rst_por_aon_n;

  // Supporting code.
  int                                                   aon_cycles;
  always @(posedge clk_aon) aon_cycles += 1;

  // Internal DUT signals.
`ifndef PATH_TO_DUT
  // The registers are in the primary partition of the rstmgr.
  `define PATH_TO_DUT tb.dut_primary
`endif

  logic [7:0] reset_info;
  always_comb begin
    reset_info = {
      `PATH_TO_DUT.u_reg.reset_info_hw_req_qs,
      `PATH_TO_DUT.u_reg.reset_info_sw_reset_qs,
      `PATH_TO_DUT.u_reg.reset_info_low_power_exit_qs,
      `PATH_TO_DUT.u_reg.reset_info_por_qs
    };
  end

  logic alert_info_en;
  always_comb alert_info_en = `PATH_TO_DUT.reg2hw.alert_info_ctrl.en.q;

  logic cpu_info_en;
  always_comb cpu_info_en = `PATH_TO_DUT.reg2hw.cpu_info_ctrl.en.q;

  bit rst_ni_inactive;
  always_comb rst_ni_inactive = resets_o.rst_lc_io_n[rstmgr_pkg::DomainMainSel];
endinterface
