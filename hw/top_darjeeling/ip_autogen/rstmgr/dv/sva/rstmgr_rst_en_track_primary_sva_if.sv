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
  input logic clk_io_i,
  input logic clk_main_i,
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
          rst_en_o.por_io[rstmgr_pkg::DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstPorIoEnTracksRstPorIoInactive_A,
          $rose(resets_o.rst_por_io_n) |-> ##DELAY
          !resets_o.rst_por_io_n ||
          rst_en_o.por_io[rstmgr_pkg::DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
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

  `ASSERT(DMainRstLcIoShadowedEnTracksRstLcIoShadowedActive_A,
          $fell(resets_o.rst_lc_io_shadowed_n) |-> ##[0:DELAY]
          rst_en_o.lc_io_shadowed[rstmgr_pkg::DomainMainSel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstLcIoShadowedEnTracksRstLcIoShadowedInactive_A,
          $rose(resets_o.rst_lc_io_shadowed_n) |-> ##DELAY
          !resets_o.rst_lc_io_shadowed_n ||
          rst_en_o.lc_io_shadowed[rstmgr_pkg::DomainMainSel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
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
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstSpiDeviceEnTracksRstSpiDeviceInactive_A,
          $rose(resets_o.rst_spi_device_n) |-> ##DELAY
          !resets_o.rst_spi_device_n ||
          rst_en_o.spi_device == prim_mubi_pkg::MuBi4False,
          clk_io_i,
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

  `ASSERT(DMainRstI2c0EnTracksRstI2c0Active_A,
          $fell(resets_o.rst_i2c0_n) |-> ##[0:DELAY]
          rst_en_o.i2c0 == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DMainRstI2c0EnTracksRstI2c0Inactive_A,
          $rose(resets_o.rst_i2c0_n) |-> ##DELAY
          !resets_o.rst_i2c0_n ||
          rst_en_o.i2c0 == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

endinterface
