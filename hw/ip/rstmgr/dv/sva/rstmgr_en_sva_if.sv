// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This has assertions that check the enables and resets match.
interface rstmgr_en_sva_if (
    input logic clk_i,
    input logic rst_ni,
    input rstmgr_pkg::rstmgr_out_t resets,
    input rstmgr_pkg::rstmgr_rst_en_t enables
);
   for (genvar i = 0; i < rstmgr_pkg::PowerDomains; ++i) begin : gen_asserts
    `ASSERT(TrackingRstEn_por_aon,
            resets.rst_por_aon_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.por_aon[i]))
    `ASSERT(TrackingRstEn_por,
            resets.rst_por_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.por[i]))
    `ASSERT(TrackingRstEn_por_io,
            resets.rst_por_io_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.por_io[i]))
    `ASSERT(TrackingRstEn_por_io_div2,
            resets.rst_por_io_div2_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.por_io_div2[i]))
    `ASSERT(TrackingRstEn_por_io_div4,
            resets.rst_por_io_div4_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.por_io_div4[i]))
    `ASSERT(TrackingRstEn_por_usb,
            resets.rst_por_usb_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.por_usb[i]))
    `ASSERT(TrackingRstEn_lc_shadowed,
            resets.rst_lc_shadowed_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.lc_shadowed[i]))
    `ASSERT(TrackingRstEn_lc,
            resets.rst_lc_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.lc[i]))
    `ASSERT(TrackingRstEn_lc_aon,
            resets.rst_lc_aon_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.lc_aon[i]))
    `ASSERT(TrackingRstEn_lc_io,
            resets.rst_lc_io_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.lc_io[i]))
    `ASSERT(TrackingRstEn_lc_io_div2,
            resets.rst_lc_io_div2_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.lc_io_div2[i]))
    `ASSERT(TrackingRstEn_lc_io_div4_shadowed,
            resets.rst_lc_io_div4_shadowed_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.lc_io_div4_shadowed[i]))
    `ASSERT(TrackingRstEn_lc_io_div4,
            resets.rst_lc_io_div4_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.lc_io_div4[i]))
    `ASSERT(TrackingRstEn_lc_usb,
            resets.rst_lc_usb_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.lc_usb[i]))
    `ASSERT(TrackingRstEn_sys,
            resets.rst_sys_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.sys[i]))
    `ASSERT(TrackingRstEn_sys_io_div4,
            resets.rst_sys_io_div4_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.sys_io_div4[i]))
    `ASSERT(TrackingRstEn_spi_device,
            resets.rst_spi_device_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.spi_device[i]))
    `ASSERT(TrackingRstEn_spi_host0,
            resets.rst_spi_host0_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.spi_host0[i]))
    `ASSERT(TrackingRstEn_spi_host1,
            resets.rst_spi_host1_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.spi_host1[i]))
    `ASSERT(TrackingRstEn_usb,
            resets.rst_usb_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.usb[i]))
    `ASSERT(TrackingRstEn_usb_aon,
            resets.rst_usb_aon_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.usb_aon[i]))
    `ASSERT(TrackingRstEn_i2c0,
            resets.rst_i2c0_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.i2c0[i]))
    `ASSERT(TrackingRstEn_i2c1,
            resets.rst_i2c1_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.i2c1[i]))
    `ASSERT(TrackingRstEn_i2c2,
            resets.rst_i2c2_n[i] == !prim_mubi_pkg::mubi4_test_true_strict(enables.i2c2[i]))
     end : gen_asserts
  endinterface : rstmgr_en_sva_if
