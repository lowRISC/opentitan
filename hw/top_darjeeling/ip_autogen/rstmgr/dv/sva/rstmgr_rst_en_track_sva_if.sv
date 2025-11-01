// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This checks that the outgoing resets and the corresponding reset enable going to alert handler
// are shifted by a single clock cycle.
interface rstmgr_rst_en_track_sva_if (
  input rstmgr_pkg::rstmgr_out_t resets_i,
  input rstmgr_pkg::rstmgr_rst_en_t reset_en_i,
  input logic clk_aon_i,
  input logic clk_io_i,
  input logic clk_main_i,
  input logic rst_por_ni
);
  import rstmgr_pkg::DomainAonSel;
  import rstmgr_pkg::Domain0Sel;
  localparam int DELAY = 1;

  `ASSERT(D0RstPorAonEnTracksRstPorAonActive_A,
          $fell(resets_i.rst_por_aon_n[Domain0Sel]) |-> ##[0:DELAY]
          reset_en_i.por_aon[Domain0Sel] == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(D0RstPorAonEnTracksRstPorAonInactive_A,
          $rose(resets_i.rst_por_aon_n[Domain0Sel]) |-> ##DELAY
          !resets_i.rst_por_aon_n[Domain0Sel] ||
          reset_en_i.por_aon[Domain0Sel] == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

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

  `ASSERT(D0RstLcShadowedEnTracksRstLcShadowedActive_A,
          $fell(resets_i.rst_lc_shadowed_n[Domain0Sel]) |-> ##[0:DELAY]
          reset_en_i.lc_shadowed[Domain0Sel] == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(D0RstLcShadowedEnTracksRstLcShadowedInactive_A,
          $rose(resets_i.rst_lc_shadowed_n[Domain0Sel]) |-> ##DELAY
          !resets_i.rst_lc_shadowed_n[Domain0Sel] ||
          reset_en_i.lc_shadowed[Domain0Sel] == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DAonRstLcShadowedEnTracksRstLcShadowedActive_A,
          $fell(resets_i.rst_lc_shadowed_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.lc_shadowed[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DAonRstLcShadowedEnTracksRstLcShadowedInactive_A,
          $rose(resets_i.rst_lc_shadowed_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_lc_shadowed_n[DomainAonSel] ||
          reset_en_i.lc_shadowed[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(DAonRstLcAonEnTracksRstLcAonActive_A,
          $fell(resets_i.rst_lc_aon_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.lc_aon[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DAonRstLcAonEnTracksRstLcAonInactive_A,
          $rose(resets_i.rst_lc_aon_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_lc_aon_n[DomainAonSel] ||
          reset_en_i.lc_aon[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(D0RstLcIoShadowedEnTracksRstLcIoShadowedActive_A,
          $fell(resets_i.rst_lc_io_shadowed_n[Domain0Sel]) |-> ##[0:DELAY]
          reset_en_i.lc_io_shadowed[Domain0Sel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(D0RstLcIoShadowedEnTracksRstLcIoShadowedInactive_A,
          $rose(resets_i.rst_lc_io_shadowed_n[Domain0Sel]) |-> ##DELAY
          !resets_i.rst_lc_io_shadowed_n[Domain0Sel] ||
          reset_en_i.lc_io_shadowed[Domain0Sel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DAonRstLcIoShadowedEnTracksRstLcIoShadowedActive_A,
          $fell(resets_i.rst_lc_io_shadowed_n[DomainAonSel]) |-> ##[0:DELAY]
          reset_en_i.lc_io_shadowed[DomainAonSel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(DAonRstLcIoShadowedEnTracksRstLcIoShadowedInactive_A,
          $rose(resets_i.rst_lc_io_shadowed_n[DomainAonSel]) |-> ##DELAY
          !resets_i.rst_lc_io_shadowed_n[DomainAonSel] ||
          reset_en_i.lc_io_shadowed[DomainAonSel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(D0RstSysEnTracksRstSysActive_A,
          $fell(resets_i.rst_sys_n[Domain0Sel]) |-> ##[0:DELAY]
          reset_en_i.sys[Domain0Sel] == prim_mubi_pkg::MuBi4True,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(D0RstSysEnTracksRstSysInactive_A,
          $rose(resets_i.rst_sys_n[Domain0Sel]) |-> ##DELAY
          !resets_i.rst_sys_n[Domain0Sel] ||
          reset_en_i.sys[Domain0Sel] == prim_mubi_pkg::MuBi4False,
          clk_main_i,
          !rst_por_ni)

  `ASSERT(D0RstSpiDeviceEnTracksRstSpiDeviceActive_A,
          $fell(resets_i.rst_spi_device_n[Domain0Sel]) |-> ##[0:DELAY]
          reset_en_i.spi_device[Domain0Sel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(D0RstSpiDeviceEnTracksRstSpiDeviceInactive_A,
          $rose(resets_i.rst_spi_device_n[Domain0Sel]) |-> ##DELAY
          !resets_i.rst_spi_device_n[Domain0Sel] ||
          reset_en_i.spi_device[Domain0Sel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(D0RstSpiHost0EnTracksRstSpiHost0Active_A,
          $fell(resets_i.rst_spi_host0_n[Domain0Sel]) |-> ##[0:DELAY]
          reset_en_i.spi_host0[Domain0Sel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(D0RstSpiHost0EnTracksRstSpiHost0Inactive_A,
          $rose(resets_i.rst_spi_host0_n[Domain0Sel]) |-> ##DELAY
          !resets_i.rst_spi_host0_n[Domain0Sel] ||
          reset_en_i.spi_host0[Domain0Sel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(D0RstI2c0EnTracksRstI2c0Active_A,
          $fell(resets_i.rst_i2c0_n[Domain0Sel]) |-> ##[0:DELAY]
          reset_en_i.i2c0[Domain0Sel] == prim_mubi_pkg::MuBi4True,
          clk_io_i,
          !rst_por_ni)

  `ASSERT(D0RstI2c0EnTracksRstI2c0Inactive_A,
          $rose(resets_i.rst_i2c0_n[Domain0Sel]) |-> ##DELAY
          !resets_i.rst_i2c0_n[Domain0Sel] ||
          reset_en_i.i2c0[Domain0Sel] == prim_mubi_pkg::MuBi4False,
          clk_io_i,
          !rst_por_ni)

endinterface
