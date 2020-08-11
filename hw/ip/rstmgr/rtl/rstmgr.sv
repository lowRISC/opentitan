// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module is the overall reset manager wrapper
// TODO: This module is only a draft implementation that covers most of the rstmgr
// functoinality but is incomplete

`include "prim_assert.sv"

// This top level controller is fairly hardcoded right now, but will be switched to a template
module rstmgr
import rstmgr_pkg::*;
(
    // Primary module clocks
    input clk_i,
    input rst_ni,
    input clk_main_i,
    input clk_io_i,
    input clk_io_div2_i,
    input clk_usb_i,
    input clk_aon_i,

    // Bus Interface
    input  tlul_pkg::tl_h2d_t tl_i,
    output tlul_pkg::tl_d2h_t tl_o,

    // pwrmgr interface
    input  pwrmgr_pkg::pwr_rst_req_t pwr_i,
    output pwrmgr_pkg::pwr_rst_rsp_t pwr_o,

    // ast interface
    input ast_wrapper_pkg::ast_rst_t ast_i,

    // cpu related inputs
    input rstmgr_cpu_t cpu_i,

    // peripheral reset requests
    input rstmgr_peri_t peri_i,

    // Interface to alert handler
    // always on resets
    output rstmgr_out_t resets_o,

    input scan_rst_ni,
    input scanmode_i

);

  localparam int NumRsts = 10;
  logic [NumRsts-1:0] raw_resets, muxed_resets;
  rstmgr_out_t resets_int;

  // receive POR and stretch
  // The por is at first stretched and synced on clk_aon
  rstmgr_por i_por (
      .clk_i (clk_aon_i),
      .rst_ni,
      .pok_i (ast_i.aon_pok),
      .rst_no(resets_int.rst_por_aon_n)
  );

  // POR usage for the clkmgr
  prim_flop_2sync #(
      .Width(1),
      .ResetValue('0)
  ) i_por_sync (
      .clk_i (clk_main_i),
      .rst_ni(resets_o.rst_por_aon_n),
      .d_i   (1'b1),
      .q_o   (resets_int.rst_por_n)
  );

  prim_flop_2sync #(
      .Width(1),
      .ResetValue('0)
  ) i_por_io_sync (
      .clk_i (clk_io_i),
      .rst_ni(resets_o.rst_por_aon_n),
      .d_i   (1'b1),
      .q_o   (resets_int.rst_por_io_n)
  );

  prim_flop_2sync #(
      .Width(1),
      .ResetValue('0)
  ) i_por_io_div2_sync (
      .clk_i (clk_io_div2_i),
      .rst_ni(resets_o.rst_por_aon_n),
      .d_i   (1'b1),
      .q_o   (resets_int.rst_por_io_div2_n)
  );

  prim_flop_2sync #(
      .Width(1),
      .ResetValue('0)
  ) i_por_usb_sync (
      .clk_i (clk_usb_i),
      .rst_ni(resets_o.rst_por_aon_n),
      .d_i   (1'b1),
      .q_o   (resets_int.rst_por_usb_n)
  );

  ////////////////////////////////////////////////////
  // Register Interface                             //
  ////////////////////////////////////////////////////

  rstmgr_reg_pkg::rstmgr_reg2hw_t reg2hw;
  rstmgr_reg_pkg::rstmgr_hw2reg_t hw2reg;

  rstmgr_reg_top u_reg (
      .clk_i,
      .rst_ni   (resets_o.rst_por_aon_n),
      .tl_i,
      .tl_o,
      .reg2hw,
      .hw2reg,
      .devmode_i(1'b1)
  );

  ////////////////////////////////////////////////////
  // Input handling                                 //
  ////////////////////////////////////////////////////

  logic ndmreset_req_q;
  logic ndm_req_valid;

  prim_flop_2sync #(
      .Width(1),
      .ResetValue('0)
  ) i_sync (
      .clk_i,
      .rst_ni(resets_o.rst_por_aon_n),
      .d_i   (cpu_i.ndmreset_req),
      .q_o   (ndmreset_req_q)
  );

  assign ndm_req_valid = ndmreset_req_q & (pwr_i.reset_cause == pwrmgr_pkg::ResetNone);

  ////////////////////////////////////////////////////
  // Source resets in the system                    //
  // These are hardcoded and not directly used.     //
  // Instead they act as async reset roots.         //
  ////////////////////////////////////////////////////
  logic [PowerDomains-1:0] rst_lc_src_n;
  logic [PowerDomains-1:0] rst_sys_src_n;

  // The two source reset modules are chained together.  The output of one is fed into the
  // the second.  This ensures that if upstream resets for any reason, the associated downstream
  // reset will also reset.

  // lc reset sources
  rstmgr_ctrl #(
      .PowerDomains(PowerDomains)
  ) i_lc_src (
      .clk_i        (clk_i),
      .rst_ni       (resets_o.rst_por_aon_n),
      .rst_req_i    (pwr_i.rst_lc_req),
      .rst_parent_ni({PowerDomains{1'b1}}),
      .rst_no       (rst_lc_src_n)
  );

  // sys reset sources
  rstmgr_ctrl #(
      .PowerDomains(PowerDomains)
  ) i_sys_src (
      .clk_i        (clk_i),
      .rst_ni       (resets_o.rst_por_aon_n),
      .rst_req_i    (pwr_i.rst_sys_req | {PowerDomains{ndm_req_valid}}),
      .rst_parent_ni(rst_lc_src_n),
      .rst_no       (rst_sys_src_n)
  );

  assign pwr_o.rst_lc_src_n = rst_lc_src_n;
  assign pwr_o.rst_sys_src_n = rst_sys_src_n;

  ////////////////////////////////////////////////////
  // leaf reset in the system                       //
  // These should all be generated                  //
  ////////////////////////////////////////////////////

  prim_flop_2sync #(
      .Width(1),
      .ResetValue('0)
  ) i_lc (
      .clk_i (clk_io_div2_i),
      .rst_ni(rst_lc_src_n[ALWAYS_ON_SEL]),
      .d_i   (1'b1),
      .q_o   (resets_int.rst_lc_n)
  );

  prim_flop_2sync #(
      .Width(1),
      .ResetValue('0)
  ) i_sys (
      .clk_i (clk_main_i),
      .rst_ni(rst_sys_src_n[ALWAYS_ON_SEL]),
      .d_i   (1'b1),
      .q_o   (resets_int.rst_sys_n)
  );

  prim_flop_2sync #(
      .Width(1),
      .ResetValue('0)
  ) i_sys_io (
      .clk_i (clk_io_div2_i),
      .rst_ni(rst_sys_src_n[ALWAYS_ON_SEL]),
      .d_i   (1'b1),
      .q_o   (resets_int.rst_sys_io_n)
  );

  prim_flop_2sync #(
      .Width(1),
      .ResetValue('0)
  ) i_spi_device (
      .clk_i (clk_io_div2_i),
      .rst_ni(rst_sys_src_n[ALWAYS_ON_SEL]),
      .d_i   (reg2hw.rst_spi_device_n.q),
      .q_o   (resets_int.rst_spi_device_n)
  );

  prim_flop_2sync #(
      .Width(1),
      .ResetValue('0)
  ) i_usb (
      .clk_i (clk_usb_i),
      .rst_ni(rst_sys_src_n[ALWAYS_ON_SEL]),
      .d_i   (reg2hw.rst_usb_n.q),
      .q_o   (resets_int.rst_usb_n)
  );

  ////////////////////////////////////////////////////
  // Reset info construction                        //
  ////////////////////////////////////////////////////

  logic [ResetReasons-1:0] rst_reqs;
  logic rst_hw_req;
  logic rst_low_power;

  assign rst_hw_req = pwr_i.reset_cause == pwrmgr_pkg::HwReq;
  assign rst_low_power = pwr_i.reset_cause == pwrmgr_pkg::LowPwrEntry;

  assign rst_reqs = {
    ndm_req_valid, rst_hw_req ? peri_i.rst_reqs : ExtResetReasons'(0), rst_low_power
  };

  rstmgr_info #(
      .Reasons(ResetReasons)
  ) i_info (
      .clk_i,
      .rst_ni       (resets_o.rst_por_aon_n),
      .rst_cpu_ni   (cpu_i.rst_cpu_n),
      .rst_req_i    (rst_reqs),
      .wr_i         (reg2hw.reset_info.qe),
      .data_i       (reg2hw.reset_info.q),
      .rst_reasons_o(hw2reg.reset_info)
  );

  ////////////////////////////////////////////////////
  // Test reset bypass                              //
  ////////////////////////////////////////////////////

  assign raw_resets = {
    resets_int.rst_por_aon_n,
    resets_int.rst_por_n,
    resets_int.rst_por_io_n,
    resets_int.rst_por_io_div2_n,
    resets_int.rst_por_usb_n,
    resets_int.rst_lc_n,
    resets_int.rst_sys_io_n,
    resets_int.rst_sys_n,
    resets_int.rst_spi_device_n,
    resets_int.rst_usb_n
  };

  assign resets_o = muxed_resets;

  // reuse clock muxes for balanced rise / fall
  for (genvar i = 0; i < NumRsts; i++) begin : gen_rst_muxes
    prim_clock_mux2 u_rst_mux (
        .clk0_i(raw_resets[i]),
        .clk1_i(scan_rst_ni),
        .sel_i (scanmode_i),
        .clk_o (muxed_resets[i])
    );
  end


  ////////////////////////////////////////////////////
  // Assertions                                     //
  ////////////////////////////////////////////////////

  // when upstream resets, downstream must also reset

endmodule  // rstmgr
