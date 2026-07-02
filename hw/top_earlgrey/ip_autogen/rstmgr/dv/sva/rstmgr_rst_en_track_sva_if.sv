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

  `OCAH_OT_ASSERT(DMainRstPorAonEnTracksRstPorAonActive_A,
          $fell(resets_i.rst_por_aon_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.por_aon[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstPorAonEnTracksRstPorAonInactive_A,
          $rose(resets_i.rst_por_aon_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_por_aon_n[DomainMainSel] ||
          reset_en_i.por_aon[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstPorAonEnTracksRstPorAonActive_A,
          $fell(resets_i.rst_por_aon_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.por_aon[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstPorAonEnTracksRstPorAonInactive_A,
          $rose(resets_i.rst_por_aon_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_por_aon_n[DomainAonSel] ||
          reset_en_i.por_aon[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstPorEnTracksRstPorActive_A,
          $fell(resets_i.rst_por_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.por[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstPorEnTracksRstPorInactive_A,
          $rose(resets_i.rst_por_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_por_n[DomainAonSel] ||
          reset_en_i.por[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstPorIoEnTracksRstPorIoActive_A,
          $fell(resets_i.rst_por_io_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.por_io[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstPorIoEnTracksRstPorIoInactive_A,
          $rose(resets_i.rst_por_io_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_por_io_n[DomainAonSel] ||
          reset_en_i.por_io[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstPorIoDiv2EnTracksRstPorIoDiv2Active_A,
          $fell(resets_i.rst_por_io_div2_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.por_io_div2[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div2_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstPorIoDiv2EnTracksRstPorIoDiv2Inactive_A,
          $rose(resets_i.rst_por_io_div2_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_por_io_div2_n[DomainAonSel] ||
          reset_en_i.por_io_div2[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div2_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstPorIoDiv4EnTracksRstPorIoDiv4Active_A,
          $fell(resets_i.rst_por_io_div4_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.por_io_div4[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstPorIoDiv4EnTracksRstPorIoDiv4Inactive_A,
          $rose(resets_i.rst_por_io_div4_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_por_io_div4_n[DomainAonSel] ||
          reset_en_i.por_io_div4[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstPorUsbEnTracksRstPorUsbActive_A,
          $fell(resets_i.rst_por_usb_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.por_usb[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_usb_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstPorUsbEnTracksRstPorUsbInactive_A,
          $rose(resets_i.rst_por_usb_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_por_usb_n[DomainAonSel] ||
          reset_en_i.por_usb[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_usb_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstLcShadowedEnTracksRstLcShadowedActive_A,
          $fell(resets_i.rst_lc_shadowed_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.lc_shadowed[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstLcShadowedEnTracksRstLcShadowedInactive_A,
          $rose(resets_i.rst_lc_shadowed_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_lc_shadowed_n[DomainMainSel] ||
          reset_en_i.lc_shadowed[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstLcShadowedEnTracksRstLcShadowedActive_A,
          $fell(resets_i.rst_lc_shadowed_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.lc_shadowed[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstLcShadowedEnTracksRstLcShadowedInactive_A,
          $rose(resets_i.rst_lc_shadowed_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_lc_shadowed_n[DomainAonSel] ||
          reset_en_i.lc_shadowed[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstLcAonEnTracksRstLcAonActive_A,
          $fell(resets_i.rst_lc_aon_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.lc_aon[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstLcAonEnTracksRstLcAonInactive_A,
          $rose(resets_i.rst_lc_aon_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_lc_aon_n[DomainAonSel] ||
          reset_en_i.lc_aon[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstLcIoEnTracksRstLcIoActive_A,
          $fell(resets_i.rst_lc_io_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.lc_io[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstLcIoEnTracksRstLcIoInactive_A,
          $rose(resets_i.rst_lc_io_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_lc_io_n[DomainAonSel] ||
          reset_en_i.lc_io[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstLcIoEnTracksRstLcIoActive_A,
          $fell(resets_i.rst_lc_io_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.lc_io[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstLcIoEnTracksRstLcIoInactive_A,
          $rose(resets_i.rst_lc_io_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_lc_io_n[DomainMainSel] ||
          reset_en_i.lc_io[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstLcIoDiv2EnTracksRstLcIoDiv2Active_A,
          $fell(resets_i.rst_lc_io_div2_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.lc_io_div2[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div2_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstLcIoDiv2EnTracksRstLcIoDiv2Inactive_A,
          $rose(resets_i.rst_lc_io_div2_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_lc_io_div2_n[DomainAonSel] ||
          reset_en_i.lc_io_div2[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div2_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstLcIoDiv2EnTracksRstLcIoDiv2Active_A,
          $fell(resets_i.rst_lc_io_div2_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.lc_io_div2[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div2_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstLcIoDiv2EnTracksRstLcIoDiv2Inactive_A,
          $rose(resets_i.rst_lc_io_div2_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_lc_io_div2_n[DomainMainSel] ||
          reset_en_i.lc_io_div2[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div2_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstLcIoDiv4ShadowedEnTracksRstLcIoDiv4ShadowedActive_A,
          $fell(resets_i.rst_lc_io_div4_shadowed_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.lc_io_div4_shadowed[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstLcIoDiv4ShadowedEnTracksRstLcIoDiv4ShadowedInactive_A,
          $rose(resets_i.rst_lc_io_div4_shadowed_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_lc_io_div4_shadowed_n[DomainMainSel] ||
          reset_en_i.lc_io_div4_shadowed[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstLcIoDiv4ShadowedEnTracksRstLcIoDiv4ShadowedActive_A,
          $fell(resets_i.rst_lc_io_div4_shadowed_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.lc_io_div4_shadowed[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstLcIoDiv4ShadowedEnTracksRstLcIoDiv4ShadowedInactive_A,
          $rose(resets_i.rst_lc_io_div4_shadowed_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_lc_io_div4_shadowed_n[DomainAonSel] ||
          reset_en_i.lc_io_div4_shadowed[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstLcUsbEnTracksRstLcUsbActive_A,
          $fell(resets_i.rst_lc_usb_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.lc_usb[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_usb_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstLcUsbEnTracksRstLcUsbInactive_A,
          $rose(resets_i.rst_lc_usb_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_lc_usb_n[DomainAonSel] ||
          reset_en_i.lc_usb[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_usb_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstLcUsbEnTracksRstLcUsbActive_A,
          $fell(resets_i.rst_lc_usb_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.lc_usb[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_usb_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstLcUsbEnTracksRstLcUsbInactive_A,
          $rose(resets_i.rst_lc_usb_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_lc_usb_n[DomainMainSel] ||
          reset_en_i.lc_usb[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_usb_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstSysEnTracksRstSysActive_A,
          $fell(resets_i.rst_sys_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.sys[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstSysEnTracksRstSysInactive_A,
          $rose(resets_i.rst_sys_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_sys_n[DomainMainSel] ||
          reset_en_i.sys[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstSysIoDiv4EnTracksRstSysIoDiv4Active_A,
          $fell(resets_i.rst_sys_io_div4_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.sys_io_div4[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DAonRstSysIoDiv4EnTracksRstSysIoDiv4Inactive_A,
          $rose(resets_i.rst_sys_io_div4_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_sys_io_div4_n[DomainAonSel] ||
          reset_en_i.sys_io_div4[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstSpiDeviceEnTracksRstSpiDeviceActive_A,
          $fell(resets_i.rst_spi_device_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.spi_device[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstSpiDeviceEnTracksRstSpiDeviceInactive_A,
          $rose(resets_i.rst_spi_device_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_spi_device_n[DomainMainSel] ||
          reset_en_i.spi_device[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstSpiHost0EnTracksRstSpiHost0Active_A,
          $fell(resets_i.rst_spi_host0_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.spi_host0[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstSpiHost0EnTracksRstSpiHost0Inactive_A,
          $rose(resets_i.rst_spi_host0_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_spi_host0_n[DomainMainSel] ||
          reset_en_i.spi_host0[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstSpiHost1EnTracksRstSpiHost1Active_A,
          $fell(resets_i.rst_spi_host1_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.spi_host1[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div2_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstSpiHost1EnTracksRstSpiHost1Inactive_A,
          $rose(resets_i.rst_spi_host1_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_spi_host1_n[DomainMainSel] ||
          reset_en_i.spi_host1[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div2_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstUsbEnTracksRstUsbActive_A,
          $fell(resets_i.rst_usb_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.usb[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_usb_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstUsbEnTracksRstUsbInactive_A,
          $rose(resets_i.rst_usb_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_usb_n[DomainMainSel] ||
          reset_en_i.usb[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_usb_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstUsbAonEnTracksRstUsbAonActive_A,
          $fell(resets_i.rst_usb_aon_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.usb_aon[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstUsbAonEnTracksRstUsbAonInactive_A,
          $rose(resets_i.rst_usb_aon_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_usb_aon_n[DomainMainSel] ||
          reset_en_i.usb_aon[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstI2c0EnTracksRstI2c0Active_A,
          $fell(resets_i.rst_i2c0_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.i2c0[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstI2c0EnTracksRstI2c0Inactive_A,
          $rose(resets_i.rst_i2c0_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_i2c0_n[DomainMainSel] ||
          reset_en_i.i2c0[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstI2c1EnTracksRstI2c1Active_A,
          $fell(resets_i.rst_i2c1_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.i2c1[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstI2c1EnTracksRstI2c1Inactive_A,
          $rose(resets_i.rst_i2c1_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_i2c1_n[DomainMainSel] ||
          reset_en_i.i2c1[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstI2c2EnTracksRstI2c2Active_A,
          $fell(resets_i.rst_i2c2_n[DomainMainSel]) |-> ##[0:DELAY]
          reset_en_i.i2c2[DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `OCAH_OT_ASSERT(DMainRstI2c2EnTracksRstI2c2Inactive_A,
          $rose(resets_i.rst_i2c2_n[DomainMainSel]) |-> ##DELAY
          !resets_i.rst_i2c2_n[DomainMainSel] ||
          reset_en_i.i2c2[DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

endinterface
