// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This checks that the outgoing resets and the corresponding reset enable going to alert handler
// are shifted by a single clock cycle.
interface rstmgr_rst_en_track_sva_if (
  input rstmgr_pkg::rstmgr_out_t resets_i,
  input rstmgr_pkg::rstmgr_rst_en_t reset_en_i,
  input logic clk_aon_i,
  input logic clk_io_div4_i,
  input logic clk_main_i,
  input logic clk_io_i,
  input logic clk_io_div2_i,
  input logic clk_usb_i,
  input logic rst_por_ni
);
  import rstmgr_pkg::DomainAonSel;
  import rstmgr_pkg::DomainMainSel;
  localparam int DELAY = 1;

  `ASSERT(DAonRstPorAonEnTracksRstPorAonActive_A,
          $fell(resets_i.rst_por_aon_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.por_aon[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorAonEnTracksRstPorAonInactive_A,
          $rose(resets_i.rst_por_aon_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_por_aon_n[DomainAonSel] ||
          reset_en_i.por_aon[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorEnTracksRstPorActive_A,
          $fell(resets_i.rst_por_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.por[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorEnTracksRstPorInactive_A,
          $rose(resets_i.rst_por_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_por_n[DomainAonSel] ||
          reset_en_i.por[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorIoEnTracksRstPorIoActive_A,
          $fell(resets_i.rst_por_io_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.por_io[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorIoEnTracksRstPorIoInactive_A,
          $rose(resets_i.rst_por_io_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_por_io_n[DomainAonSel] ||
          reset_en_i.por_io[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorIoDiv2EnTracksRstPorIoDiv2Active_A,
          $fell(resets_i.rst_por_io_div2_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.por_io_div2[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div2_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorIoDiv2EnTracksRstPorIoDiv2Inactive_A,
          $rose(resets_i.rst_por_io_div2_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_por_io_div2_n[DomainAonSel] ||
          reset_en_i.por_io_div2[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div2_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorIoDiv4ShadowedEnTracksRstPorIoDiv4ShadowedActive_A,
          $fell(resets_i.rst_por_io_div4_shadowed_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.por_io_div4_shadowed[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorIoDiv4ShadowedEnTracksRstPorIoDiv4ShadowedInactive_A,
          $rose(resets_i.rst_por_io_div4_shadowed_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_por_io_div4_shadowed_n[DomainAonSel] ||
          reset_en_i.por_io_div4_shadowed[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorUsbEnTracksRstPorUsbActive_A,
          $fell(resets_i.rst_por_usb_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.por_usb[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_usb_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorUsbEnTracksRstPorUsbInactive_A,
          $rose(resets_i.rst_por_usb_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_por_usb_n[DomainAonSel] ||
          reset_en_i.por_usb[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_usb_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcShadowedEnTracksRstLcShadowedActive_A,
          $fell(resets_i.rst_lc_shadowed_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.lc_shadowed[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcShadowedEnTracksRstLcShadowedInactive_A,
          $rose(resets_i.rst_lc_shadowed_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_lc_shadowed_n[DomainMainSel] ||
          reset_en_i.lc_shadowed[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcIoDiv4EnTracksRstLcIoDiv4Active_A,
          $fell(resets_i.rst_lc_io_div4_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.lc_io_div4[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcIoDiv4EnTracksRstLcIoDiv4Inactive_A,
          $rose(resets_i.rst_lc_io_div4_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_lc_io_div4_n[DomainMainSel] ||
          reset_en_i.lc_io_div4[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DAonRstLcIoDiv4EnTracksRstLcIoDiv4Active_A,
          $fell(resets_i.rst_lc_io_div4_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.lc_io_div4[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DAonRstLcIoDiv4EnTracksRstLcIoDiv4Inactive_A,
          $rose(resets_i.rst_lc_io_div4_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_lc_io_div4_n[DomainAonSel] ||
          reset_en_i.lc_io_div4[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstSysShadowedEnTracksRstSysShadowedActive_A,
          $fell(resets_i.rst_sys_shadowed_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.sys_shadowed[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DMainRstSysShadowedEnTracksRstSysShadowedInactive_A,
          $rose(resets_i.rst_sys_shadowed_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_sys_shadowed_n[DomainMainSel] ||
          reset_en_i.sys_shadowed[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DMainRstSysIoDiv4EnTracksRstSysIoDiv4Active_A,
          $fell(resets_i.rst_sys_io_div4_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.sys_io_div4[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstSysIoDiv4EnTracksRstSysIoDiv4Inactive_A,
          $rose(resets_i.rst_sys_io_div4_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_sys_io_div4_n[DomainMainSel] ||
          reset_en_i.sys_io_div4[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DAonRstSysIoDiv4EnTracksRstSysIoDiv4Active_A,
          $fell(resets_i.rst_sys_io_div4_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.sys_io_div4[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DAonRstSysIoDiv4EnTracksRstSysIoDiv4Inactive_A,
          $rose(resets_i.rst_sys_io_div4_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_sys_io_div4_n[DomainAonSel] ||
          reset_en_i.sys_io_div4[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstSysAonEnTracksRstSysAonActive_A,
          $fell(resets_i.rst_sys_aon_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.sys_aon[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DMainRstSysAonEnTracksRstSysAonInactive_A,
          $rose(resets_i.rst_sys_aon_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_sys_aon_n[DomainMainSel] ||
          reset_en_i.sys_aon[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DAonRstSysAonEnTracksRstSysAonActive_A,
          $fell(resets_i.rst_sys_aon_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.sys_aon[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DAonRstSysAonEnTracksRstSysAonInactive_A,
          $rose(resets_i.rst_sys_aon_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_sys_aon_n[DomainAonSel] ||
          reset_en_i.sys_aon[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DMainRstSpiDeviceEnTracksRstSpiDeviceActive_A,
          $fell(resets_i.rst_spi_device_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.spi_device[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div2_i,
          !rst_por_ni)

  `ASSERT(DMainRstSpiDeviceEnTracksRstSpiDeviceInactive_A,
          $rose(resets_i.rst_spi_device_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_spi_device_n[DomainMainSel] ||
          reset_en_i.spi_device[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div2_i,
          !rst_por_ni)

  `ASSERT(DMainRstSpiHost0EnTracksRstSpiHost0Active_A,
          $fell(resets_i.rst_spi_host0_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.spi_host0[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstSpiHost0EnTracksRstSpiHost0Inactive_A,
          $rose(resets_i.rst_spi_host0_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_spi_host0_n[DomainMainSel] ||
          reset_en_i.spi_host0[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstUsbEnTracksRstUsbActive_A,
          $fell(resets_i.rst_usb_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.usb[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_usb_i,
          !rst_por_ni)

  `ASSERT(DMainRstUsbEnTracksRstUsbInactive_A,
          $rose(resets_i.rst_usb_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_usb_n[DomainMainSel] ||
          reset_en_i.usb[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_usb_i,
          !rst_por_ni)

endinterface
