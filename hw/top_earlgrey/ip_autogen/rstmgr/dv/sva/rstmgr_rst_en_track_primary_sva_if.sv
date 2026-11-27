// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The indication checks of the single power-domain reset manager, for the resets that the primary
// partition generates. rstmgr_bind binds this interface to rstmgr_part_primary.
// rstmgr_rst_en_track_secondary_sva_if has the checks of the resets that the secondary partition
// generates.

// This checks that the outgoing resets and the corresponding reset enable going to alert handler
// are shifted by a single clock cycle.
interface rstmgr_rst_en_track_primary_sva_if (
  input logic clk_aon_i,
  input logic clk_io_div4_i,
  input logic clk_main_i,
  input logic clk_io_i,
  input logic clk_usb_i,
  input logic rst_por_ni,
  input rstmgr_pkg::rstmgr_out_primary_t resets_o,
  input rstmgr_pkg::rstmgr_rst_en_primary_t rst_en_o
);
  localparam int DELAY = 1;

  `ASSERT(DMainRstPorEnTracksRstPorActive_A,
          $fell(resets_o.rst_por_n) |-> ##[0:DELAY]
          rst_en_o.por == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DMainRstPorEnTracksRstPorInactive_A,
          $rose(resets_o.rst_por_n) |-> ##DELAY
          !resets_o.rst_por_n ||
          rst_en_o.por == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DMainRstPorIoEnTracksRstPorIoActive_A,
          $fell(resets_o.rst_por_io_n) |-> ##[0:DELAY]
          rst_en_o.por_io == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstPorIoEnTracksRstPorIoInactive_A,
          $rose(resets_o.rst_por_io_n) |-> ##DELAY
          !resets_o.rst_por_io_n ||
          rst_en_o.por_io == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstPorIoDiv4EnTracksRstPorIoDiv4Active_A,
          $fell(resets_o.rst_por_io_div4_n) |-> ##[0:DELAY]
          rst_en_o.por_io_div4[rstmgr_pkg::DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstPorIoDiv4EnTracksRstPorIoDiv4Inactive_A,
          $rose(resets_o.rst_por_io_div4_n) |-> ##DELAY
          !resets_o.rst_por_io_div4_n ||
          rst_en_o.por_io_div4[rstmgr_pkg::DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstPorUsbEnTracksRstPorUsbActive_A,
          $fell(resets_o.rst_por_usb_n) |-> ##[0:DELAY]
          rst_en_o.por_usb == prim_mubi_pkg::MuBi4True,
          clk_usb_i,
          !rst_por_ni)

  `ASSERT(DMainRstPorUsbEnTracksRstPorUsbInactive_A,
          $rose(resets_o.rst_por_usb_n) |-> ##DELAY
          !resets_o.rst_por_usb_n ||
          rst_en_o.por_usb == prim_mubi_pkg::MuBi4False,
          clk_usb_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcShadowedEnTracksRstLcShadowedActive_A,
          $fell(resets_o.rst_lc_shadowed_n) |-> ##[0:DELAY]
          rst_en_o.lc_shadowed == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcShadowedEnTracksRstLcShadowedInactive_A,
          $rose(resets_o.rst_lc_shadowed_n) |-> ##DELAY
          !resets_o.rst_lc_shadowed_n ||
          rst_en_o.lc_shadowed == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcAonEnTracksRstLcAonActive_A,
          $fell(resets_o.rst_lc_aon_n) |-> ##[0:DELAY]
          rst_en_o.lc_aon[rstmgr_pkg::DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcAonEnTracksRstLcAonInactive_A,
          $rose(resets_o.rst_lc_aon_n) |-> ##DELAY
          !resets_o.rst_lc_aon_n ||
          rst_en_o.lc_aon[rstmgr_pkg::DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcIoEnTracksRstLcIoActive_A,
          $fell(resets_o.rst_lc_io_n) |-> ##[0:DELAY]
          rst_en_o.lc_io == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcIoEnTracksRstLcIoInactive_A,
          $rose(resets_o.rst_lc_io_n) |-> ##DELAY
          !resets_o.rst_lc_io_n ||
          rst_en_o.lc_io == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcIoDiv4ShadowedEnTracksRstLcIoDiv4ShadowedActive_A,
          $fell(resets_o.rst_lc_io_div4_shadowed_n) |-> ##[0:DELAY]
          rst_en_o.lc_io_div4_shadowed[rstmgr_pkg::DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcIoDiv4ShadowedEnTracksRstLcIoDiv4ShadowedInactive_A,
          $rose(resets_o.rst_lc_io_div4_shadowed_n) |-> ##DELAY
          !resets_o.rst_lc_io_div4_shadowed_n ||
          rst_en_o.lc_io_div4_shadowed[rstmgr_pkg::DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcUsbEnTracksRstLcUsbActive_A,
          $fell(resets_o.rst_lc_usb_n) |-> ##[0:DELAY]
          rst_en_o.lc_usb == prim_mubi_pkg::MuBi4True,
          clk_usb_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcUsbEnTracksRstLcUsbInactive_A,
          $rose(resets_o.rst_lc_usb_n) |-> ##DELAY
          !resets_o.rst_lc_usb_n ||
          rst_en_o.lc_usb == prim_mubi_pkg::MuBi4False,
          clk_usb_i,
          !rst_por_ni)

  `ASSERT(DMainRstSysEnTracksRstSysActive_A,
          $fell(resets_o.rst_sys_n) |-> ##[0:DELAY]
          rst_en_o.sys == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DMainRstSysEnTracksRstSysInactive_A,
          $rose(resets_o.rst_sys_n) |-> ##DELAY
          !resets_o.rst_sys_n ||
          rst_en_o.sys == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DMainRstSpiDeviceEnTracksRstSpiDeviceActive_A,
          $fell(resets_o.rst_spi_device_n) |-> ##[0:DELAY]
          rst_en_o.spi_device == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstSpiDeviceEnTracksRstSpiDeviceInactive_A,
          $rose(resets_o.rst_spi_device_n) |-> ##DELAY
          !resets_o.rst_spi_device_n ||
          rst_en_o.spi_device == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstSpiHost0EnTracksRstSpiHost0Active_A,
          $fell(resets_o.rst_spi_host0_n) |-> ##[0:DELAY]
          rst_en_o.spi_host0 == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstSpiHost0EnTracksRstSpiHost0Inactive_A,
          $rose(resets_o.rst_spi_host0_n) |-> ##DELAY
          !resets_o.rst_spi_host0_n ||
          rst_en_o.spi_host0 == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstSpiHost1EnTracksRstSpiHost1Active_A,
          $fell(resets_o.rst_spi_host1_n) |-> ##[0:DELAY]
          rst_en_o.spi_host1 == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstSpiHost1EnTracksRstSpiHost1Inactive_A,
          $rose(resets_o.rst_spi_host1_n) |-> ##DELAY
          !resets_o.rst_spi_host1_n ||
          rst_en_o.spi_host1 == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstUsbEnTracksRstUsbActive_A,
          $fell(resets_o.rst_usb_n) |-> ##[0:DELAY]
          rst_en_o.usb == prim_mubi_pkg::MuBi4True,
          clk_usb_i,
          !rst_por_ni)

  `ASSERT(DMainRstUsbEnTracksRstUsbInactive_A,
          $rose(resets_o.rst_usb_n) |-> ##DELAY
          !resets_o.rst_usb_n ||
          rst_en_o.usb == prim_mubi_pkg::MuBi4False,
          clk_usb_i,
          !rst_por_ni)

  `ASSERT(DMainRstUsbAonEnTracksRstUsbAonActive_A,
          $fell(resets_o.rst_usb_aon_n) |-> ##[0:DELAY]
          rst_en_o.usb_aon == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DMainRstUsbAonEnTracksRstUsbAonInactive_A,
          $rose(resets_o.rst_usb_aon_n) |-> ##DELAY
          !resets_o.rst_usb_aon_n ||
          rst_en_o.usb_aon == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DMainRstI2c0EnTracksRstI2c0Active_A,
          $fell(resets_o.rst_i2c0_n) |-> ##[0:DELAY]
          rst_en_o.i2c0 == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstI2c0EnTracksRstI2c0Inactive_A,
          $rose(resets_o.rst_i2c0_n) |-> ##DELAY
          !resets_o.rst_i2c0_n ||
          rst_en_o.i2c0 == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstI2c1EnTracksRstI2c1Active_A,
          $fell(resets_o.rst_i2c1_n) |-> ##[0:DELAY]
          rst_en_o.i2c1 == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstI2c1EnTracksRstI2c1Inactive_A,
          $rose(resets_o.rst_i2c1_n) |-> ##DELAY
          !resets_o.rst_i2c1_n ||
          rst_en_o.i2c1 == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstI2c2EnTracksRstI2c2Active_A,
          $fell(resets_o.rst_i2c2_n) |-> ##[0:DELAY]
          rst_en_o.i2c2 == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstI2c2EnTracksRstI2c2Inactive_A,
          $rose(resets_o.rst_i2c2_n) |-> ##DELAY
          !resets_o.rst_i2c2_n ||
          rst_en_o.i2c2 == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DMainRstI3c0EnTracksRstI3c0Active_A,
          $fell(resets_o.rst_i3c0_n) |-> ##[0:DELAY]
          rst_en_o.i3c0 == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstI3c0EnTracksRstI3c0Inactive_A,
          $rose(resets_o.rst_i3c0_n) |-> ##DELAY
          !resets_o.rst_i3c0_n ||
          rst_en_o.i3c0 == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstI3c1EnTracksRstI3c1Active_A,
          $fell(resets_o.rst_i3c1_n) |-> ##[0:DELAY]
          rst_en_o.i3c1 == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstI3c1EnTracksRstI3c1Inactive_A,
          $rose(resets_o.rst_i3c1_n) |-> ##DELAY
          !resets_o.rst_i3c1_n ||
          rst_en_o.i3c1 == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

endinterface
