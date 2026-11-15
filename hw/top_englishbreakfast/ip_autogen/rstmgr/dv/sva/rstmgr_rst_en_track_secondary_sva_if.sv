// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The indication checks of the single power-domain reset manager, for the resets that the secondary
// partition generates. rstmgr_bind binds this interface to rstmgr_part_secondary.
// rstmgr_rst_en_track_primary_sva_if has the checks of the resets that the primary partition
// generates.

// This checks that the outgoing resets and the corresponding reset enable going to alert handler
// are shifted by a single clock cycle.
interface rstmgr_rst_en_track_secondary_sva_if (
  input logic clk_aon_i,
  input logic clk_io_div4_i,
  input logic rst_por_ni,
  input rstmgr_pkg::rstmgr_out_secondary_t resets_secondary_o,
  input rstmgr_pkg::intraip_s2p_t intraip_s2p_o
);
  localparam int DELAY = 1;

  `ASSERT(DAonRstPorAonEnTracksRstPorAonActive_A,
          $fell(resets_secondary_o.rst_por_aon_n[rstmgr_pkg::DomainAonSel]) |-> ##[0:DELAY]
          intraip_s2p_o.rst_en_por_aon_aon == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorAonEnTracksRstPorAonInactive_A,
          $rose(resets_secondary_o.rst_por_aon_n[rstmgr_pkg::DomainAonSel]) |-> ##DELAY
          !resets_secondary_o.rst_por_aon_n[rstmgr_pkg::DomainAonSel] ||
          intraip_s2p_o.rst_en_por_aon_aon == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DMainRstPorAonEnTracksRstPorAonActive_A,
          $fell(resets_secondary_o.rst_por_aon_n[rstmgr_pkg::DomainMainSel]) |-> ##[0:DELAY]
          intraip_s2p_o.rst_en_por_aon_main == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DMainRstPorAonEnTracksRstPorAonInactive_A,
          $rose(resets_secondary_o.rst_por_aon_n[rstmgr_pkg::DomainMainSel]) |-> ##DELAY
          !resets_secondary_o.rst_por_aon_n[rstmgr_pkg::DomainMainSel] ||
          intraip_s2p_o.rst_en_por_aon_main == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorIoDiv4ShadowedEnTracksRstPorIoDiv4ShadowedActive_A,
          $fell(resets_secondary_o.rst_por_io_div4_shadowed_n) |-> ##[0:DELAY]
          intraip_s2p_o.rst_en_por_io_div4_shadowed_aon == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DAonRstPorIoDiv4ShadowedEnTracksRstPorIoDiv4ShadowedInactive_A,
          $rose(resets_secondary_o.rst_por_io_div4_shadowed_n) |-> ##DELAY
          !resets_secondary_o.rst_por_io_div4_shadowed_n ||
          intraip_s2p_o.rst_en_por_io_div4_shadowed_aon == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DAonRstLcIoDiv4EnTracksRstLcIoDiv4Active_A,
          $fell(resets_secondary_o.rst_lc_io_div4_n) |-> ##[0:DELAY]
          intraip_s2p_o.rst_en_lc_io_div4_aon == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DAonRstLcIoDiv4EnTracksRstLcIoDiv4Inactive_A,
          $rose(resets_secondary_o.rst_lc_io_div4_n) |-> ##DELAY
          !resets_secondary_o.rst_lc_io_div4_n ||
          intraip_s2p_o.rst_en_lc_io_div4_aon == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DAonRstSysIoDiv4EnTracksRstSysIoDiv4Active_A,
          $fell(resets_secondary_o.rst_sys_io_div4_n) |-> ##[0:DELAY]
          intraip_s2p_o.rst_en_sys_io_div4_aon == prim_mubi_pkg::MuBi4True,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DAonRstSysIoDiv4EnTracksRstSysIoDiv4Inactive_A,
          $rose(resets_secondary_o.rst_sys_io_div4_n) |-> ##DELAY
          !resets_secondary_o.rst_sys_io_div4_n ||
          intraip_s2p_o.rst_en_sys_io_div4_aon == prim_mubi_pkg::MuBi4False,
          clk_io_div4_i,
          !rst_por_ni)

  `ASSERT(DAonRstSysAonEnTracksRstSysAonActive_A,
          $fell(resets_secondary_o.rst_sys_aon_n) |-> ##[0:DELAY]
          intraip_s2p_o.rst_en_sys_aon_aon == prim_mubi_pkg::MuBi4True,
          clk_aon_i,
          !rst_por_ni)

  `ASSERT(DAonRstSysAonEnTracksRstSysAonInactive_A,
          $rose(resets_secondary_o.rst_sys_aon_n) |-> ##DELAY
          !resets_secondary_o.rst_sys_aon_n ||
          intraip_s2p_o.rst_en_sys_aon_aon == prim_mubi_pkg::MuBi4False,
          clk_aon_i,
          !rst_por_ni)

endinterface
