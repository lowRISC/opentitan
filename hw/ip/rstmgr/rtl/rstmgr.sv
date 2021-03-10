// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module is the overall reset manager wrapper
// TODO: This module is only a draft implementation that covers most of the rstmgr
// functoinality but is incomplete

`include "prim_assert.sv"

// This top level controller is fairly hardcoded right now, but will be switched to a template
module rstmgr import rstmgr_pkg::*; (
  // Primary module clocks
  input clk_i,
  input rst_ni, // this is currently connected to top level reset, but will change once ast is in
  input clk_aon_i,
  input clk_io_div4_i,
  input clk_main_i,
  input clk_io_i,
  input clk_io_div2_i,
  input clk_usb_i,

  // Bus Interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // pwrmgr interface
  input pwrmgr_pkg::pwr_rst_req_t pwr_i,
  output pwrmgr_pkg::pwr_rst_rsp_t pwr_o,

  // ast interface
  input rstmgr_ast_t ast_i,

  // cpu related inputs
  input rstmgr_cpu_t cpu_i,

  // Interface to alert handler
  input alert_pkg::alert_crashdump_t alert_dump_i,

  // dft bypass
  input scan_rst_ni,
  input scanmode_i,

  // reset outputs
  output rstmgr_ast_out_t resets_ast_o,
  output rstmgr_out_t resets_o

);

  import rstmgr_reg_pkg::*;

  // receive POR and stretch
  // The por is at first stretched and synced on clk_aon
  // The rst_ni and pok_i input will be changed once AST is integrated
  logic [PowerDomains-1:0] rst_por_aon_n;

  for (genvar i = 0; i < PowerDomains; i++) begin : gen_rst_por_aon
    if (i == DomainAonSel) begin : gen_rst_por_aon_normal
      rstmgr_por u_rst_por_aon (
        .clk_i(clk_aon_i),
        .rst_ni(ast_i.aon_pok),
        .scan_rst_ni,
        .scanmode_i,
        .rst_no(rst_por_aon_n[i])
      );

      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_rst_por_aon_n_mux (
        .clk0_i(rst_por_aon_n[i]),
        .clk1_i(scan_rst_ni),
        .sel_i(scanmode_i),
        .clk_o(resets_o.rst_por_aon_n[i])
      );
    end else begin : gen_rst_por_aon_tieoff
      assign rst_por_aon_n[i] = 1'b0;
      assign resets_o.rst_por_aon_n[i] = rst_por_aon_n[i];
    end
  end


  ////////////////////////////////////////////////////
  // Register Interface                             //
  ////////////////////////////////////////////////////

  // local_rst_n is the reset used by the rstmgr for its internal logic
  logic local_rst_n;
  assign local_rst_n = resets_o.rst_por_io_div2_n[DomainAonSel];

  rstmgr_reg_pkg::rstmgr_reg2hw_t reg2hw;
  rstmgr_reg_pkg::rstmgr_hw2reg_t hw2reg;

  rstmgr_reg_top u_reg (
    .clk_i,
    .rst_ni(local_rst_n),
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
  ) u_sync (
    .clk_i,
    .rst_ni(local_rst_n),
    .d_i(cpu_i.ndmreset_req),
    .q_o(ndmreset_req_q)
  );

  assign ndm_req_valid = ndmreset_req_q & (pwr_i.reset_cause == pwrmgr_pkg::ResetNone);

  ////////////////////////////////////////////////////
  // Source resets in the system                    //
  // These are hardcoded and not directly used.     //
  // Instead they act as async reset roots.         //
  ////////////////////////////////////////////////////

  // The two source reset modules are chained together.  The output of one is fed into the
  // the second.  This ensures that if upstream resets for any reason, the associated downstream
  // reset will also reset.

  logic [PowerDomains-1:0] rst_lc_src_n;
  logic [PowerDomains-1:0] rst_sys_src_n;


  // lc reset sources
  rstmgr_ctrl u_lc_src (
    .clk_i,
    .rst_ni(local_rst_n),
    .rst_req_i(pwr_i.rst_lc_req),
    .rst_parent_ni({PowerDomains{1'b1}}),
    .rst_no(rst_lc_src_n)
  );

  // sys reset sources
  rstmgr_ctrl u_sys_src (
    .clk_i,
    .rst_ni(local_rst_n),
    .rst_req_i(pwr_i.rst_sys_req | {PowerDomains{ndm_req_valid}}),
    .rst_parent_ni(rst_lc_src_n),
    .rst_no(rst_sys_src_n)
  );

  assign pwr_o.rst_lc_src_n = rst_lc_src_n;
  assign pwr_o.rst_sys_src_n = rst_sys_src_n;


  ////////////////////////////////////////////////////
  // Software reset controls external reg           //
  ////////////////////////////////////////////////////
  logic [NumSwResets-1:0] sw_rst_ctrl_n;

  for (genvar i=0; i < NumSwResets; i++) begin : gen_sw_rst_ext_regs
    prim_subreg #(
      .DW(1),
      .SWACCESS("RW"),
      .RESVAL(1)
    ) u_rst_sw_ctrl_reg (
      .clk_i,
      .rst_ni(local_rst_n),
      .we(reg2hw.sw_rst_ctrl_n[i].qe & reg2hw.sw_rst_regen[i]),
      .wd(reg2hw.sw_rst_ctrl_n[i].q),
      .de('0),
      .d('0),
      .qe(),
      .q(sw_rst_ctrl_n[i]),
      .qs(hw2reg.sw_rst_ctrl_n[i].d)
    );
  end

  ////////////////////////////////////////////////////
  // leaf reset in the system                       //
  // These should all be generated                  //
  ////////////////////////////////////////////////////
  // To simplify generation, each reset generates all associated power domain outputs.
  // If a reset does not support a particular power domain, that reset is always hard-wired to 0.

  logic [PowerDomains-1:0] rst_por_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_por (
    .clk_i(clk_main_i),
    .rst_ni(rst_por_aon_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_por_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_por_mux (
    .clk0_i(rst_por_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_por_n[DomainAonSel])
  );

  assign rst_por_n[Domain0Sel] = 1'b0;
  assign resets_o.rst_por_n[Domain0Sel] = rst_por_n[Domain0Sel];


  logic [PowerDomains-1:0] rst_por_io_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_por_io (
    .clk_i(clk_io_i),
    .rst_ni(rst_por_aon_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_por_io_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_por_io_mux (
    .clk0_i(rst_por_io_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_por_io_n[DomainAonSel])
  );

  assign rst_por_io_n[Domain0Sel] = 1'b0;
  assign resets_o.rst_por_io_n[Domain0Sel] = rst_por_io_n[Domain0Sel];


  logic [PowerDomains-1:0] rst_por_io_div2_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_por_io_div2 (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_por_aon_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_por_io_div2_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_por_io_div2_mux (
    .clk0_i(rst_por_io_div2_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_por_io_div2_n[DomainAonSel])
  );

  assign rst_por_io_div2_n[Domain0Sel] = 1'b0;
  assign resets_o.rst_por_io_div2_n[Domain0Sel] = rst_por_io_div2_n[Domain0Sel];


  logic [PowerDomains-1:0] rst_por_io_div4_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_por_io_div4 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_por_aon_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_por_io_div4_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_por_io_div4_mux (
    .clk0_i(rst_por_io_div4_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_por_io_div4_n[DomainAonSel])
  );

  assign rst_por_io_div4_n[Domain0Sel] = 1'b0;
  assign resets_o.rst_por_io_div4_n[Domain0Sel] = rst_por_io_div4_n[Domain0Sel];


  logic [PowerDomains-1:0] rst_por_usb_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_por_usb (
    .clk_i(clk_usb_i),
    .rst_ni(rst_por_aon_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_por_usb_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_por_usb_mux (
    .clk0_i(rst_por_usb_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_por_usb_n[DomainAonSel])
  );

  assign rst_por_usb_n[Domain0Sel] = 1'b0;
  assign resets_o.rst_por_usb_n[Domain0Sel] = rst_por_usb_n[Domain0Sel];


  logic [PowerDomains-1:0] rst_lc_n;
  assign rst_lc_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_lc_n[DomainAonSel] = rst_lc_n[DomainAonSel];


  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_lc (
    .clk_i(clk_main_i),
    .rst_ni(rst_lc_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_lc_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_lc_mux (
    .clk0_i(rst_lc_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_lc_n[Domain0Sel])
  );

  logic [PowerDomains-1:0] rst_lc_io_div4_n;
  assign rst_lc_io_div4_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_lc_io_div4_n[DomainAonSel] = rst_lc_io_div4_n[DomainAonSel];


  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_lc_io_div4 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_lc_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_lc_io_div4_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_lc_io_div4_mux (
    .clk0_i(rst_lc_io_div4_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_lc_io_div4_n[Domain0Sel])
  );

  logic [PowerDomains-1:0] rst_sys_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_sys (
    .clk_i(clk_main_i),
    .rst_ni(rst_sys_src_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_sys_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_sys_mux (
    .clk0_i(rst_sys_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_sys_n[DomainAonSel])
  );

  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_sys (
    .clk_i(clk_main_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_sys_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_sys_mux (
    .clk0_i(rst_sys_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_sys_n[Domain0Sel])
  );

  logic [PowerDomains-1:0] rst_sys_io_n;
  assign rst_sys_io_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_sys_io_n[DomainAonSel] = rst_sys_io_n[DomainAonSel];


  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_sys_io (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_sys_io_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_sys_io_mux (
    .clk0_i(rst_sys_io_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_sys_io_n[Domain0Sel])
  );

  logic [PowerDomains-1:0] rst_sys_io_div4_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_sys_io_div4 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_src_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_sys_io_div4_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_sys_io_div4_mux (
    .clk0_i(rst_sys_io_div4_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_sys_io_div4_n[DomainAonSel])
  );

  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_sys_io_div4 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_sys_io_div4_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_sys_io_div4_mux (
    .clk0_i(rst_sys_io_div4_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_sys_io_div4_n[Domain0Sel])
  );

  logic [PowerDomains-1:0] rst_sys_aon_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_sys_aon (
    .clk_i(clk_aon_i),
    .rst_ni(rst_sys_src_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_sys_aon_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_sys_aon_mux (
    .clk0_i(rst_sys_aon_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_sys_aon_n[DomainAonSel])
  );

  assign rst_sys_aon_n[Domain0Sel] = 1'b0;
  assign resets_o.rst_sys_aon_n[Domain0Sel] = rst_sys_aon_n[Domain0Sel];


  logic [PowerDomains-1:0] rst_spi_device_n;
  assign rst_spi_device_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_spi_device_n[DomainAonSel] = rst_spi_device_n[DomainAonSel];


  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_spi_device (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(sw_rst_ctrl_n[SPI_DEVICE]),
    .q_o(rst_spi_device_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_spi_device_mux (
    .clk0_i(rst_spi_device_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_spi_device_n[Domain0Sel])
  );

  logic [PowerDomains-1:0] rst_usb_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_usb (
    .clk_i(clk_usb_i),
    .rst_ni(rst_sys_src_n[DomainAonSel]),
    .d_i(sw_rst_ctrl_n[USB]),
    .q_o(rst_usb_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_usb_mux (
    .clk0_i(rst_usb_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(resets_o.rst_usb_n[DomainAonSel])
  );

  assign rst_usb_n[Domain0Sel] = 1'b0;
  assign resets_o.rst_usb_n[Domain0Sel] = rst_usb_n[Domain0Sel];



  ////////////////////////////////////////////////////
  // Reset info construction                        //
  ////////////////////////////////////////////////////

  logic rst_hw_req;
  logic rst_low_power;
  logic rst_ndm;
  logic rst_cpu_nq;
  logic first_reset;

  // The qualification of first reset below could technically be POR as well.
  // However, that would enforce software to clear POR upon cold power up.  While that is
  // the most likely outcome anyways, hardware should not require that.
  assign rst_hw_req    = ~first_reset & pwr_i.reset_cause == pwrmgr_pkg::HwReq;
  assign rst_ndm       = ~first_reset & ndm_req_valid;
  assign rst_low_power = ~first_reset & pwr_i.reset_cause == pwrmgr_pkg::LowPwrEntry;

  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_cpu_reset_synced (
    .clk_i,
    .rst_ni(local_rst_n),
    .d_i(cpu_i.rst_cpu_n),
    .q_o(rst_cpu_nq)
  );

  // first reset is a flag that blocks reset recording until first de-assertion
  always_ff @(posedge clk_i or negedge local_rst_n) begin
    if (!local_rst_n) begin
      first_reset <= 1'b1;
    end else if (rst_cpu_nq) begin
      first_reset <= 1'b0;
    end
  end

  // Only sw is allowed to clear a reset reason, hw is only allowed to set it.
  assign hw2reg.reset_info.low_power_exit.d  = 1'b1;
  assign hw2reg.reset_info.low_power_exit.de = rst_low_power;

  assign hw2reg.reset_info.ndm_reset.d  = 1'b1;
  assign hw2reg.reset_info.ndm_reset.de = rst_ndm;

  // HW reset requests most likely will be multi-bit, so OR in whatever reasons
  // that are already set.
  assign hw2reg.reset_info.hw_req.d  = pwr_i.rstreqs | reg2hw.reset_info.hw_req.q;
  assign hw2reg.reset_info.hw_req.de = rst_hw_req;


  ////////////////////////////////////////////////////
  // Exported resets                                //
  ////////////////////////////////////////////////////
  assign resets_ast_o.rst_ast_usbdev_sys_io_div4_n = resets_o.rst_sys_io_div4_n;
  assign resets_ast_o.rst_ast_usbdev_usb_n = resets_o.rst_usb_n;
  assign resets_ast_o.rst_ast_sensor_ctrl_sys_io_div4_n = resets_o.rst_sys_io_div4_n;

  ////////////////////////////////////////////////////
  // Crash info capture                             //
  ////////////////////////////////////////////////////
  localparam int CrashRemainder = $bits(alert_pkg::alert_crashdump_t) % RdWidth > 0 ? 1 : 0;
  localparam int CrashStoreSlot = $bits(alert_pkg::alert_crashdump_t) / RdWidth +
      CrashRemainder;
  localparam int TotalWidth     = CrashStoreSlot * RdWidth;
  localparam int SlotCntWidth   = $clog2(CrashStoreSlot);

  logic dump_capture;
  logic [2**SlotCntWidth-1:0][RdWidth-1:0] slots;
  logic [CrashStoreSlot-1:0][RdWidth-1:0] slots_q;

  // capture on any legal reset request
  assign dump_capture = reg2hw.alert_info_ctrl.en.q &
                        (rst_hw_req | rst_ndm | rst_low_power);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      slots_q <= '0;
    end else if (dump_capture) begin
      slots_q <= TotalWidth'(alert_dump_i);
    end
  end

  always_comb begin
    slots = '0;
    slots[CrashStoreSlot-1:0] = slots_q;
  end

  // once dump is captured, no more information is captured until
  // re-eanbled by software.
  assign hw2reg.alert_info_ctrl.en.d  = 1'b0;
  assign hw2reg.alert_info_ctrl.en.de = dump_capture;

  // number of segments to read
  assign hw2reg.alert_info_attr.d = CrashStoreSlot;

  // the actual dump data
  assign hw2reg.alert_info.d = slots[reg2hw.alert_info_ctrl.index.q[SlotCntWidth-1:0]];

  if (SlotCntWidth < IdxWidth) begin : gen_tieoffs
    logic [IdxWidth-SlotCntWidth-1:0] unused_idx;
    assign unused_idx = reg2hw.alert_info_ctrl.index.q[IdxWidth-1:SlotCntWidth];
  end


  ////////////////////////////////////////////////////
  // Assertions                                     //
  ////////////////////////////////////////////////////

  // Make sure the crash dump isn't excessively large
  `ASSERT_INIT(CntWidth_A, SlotCntWidth <= IdxWidth)

  // when upstream resets, downstream must also reset

  // output known asserts
  `ASSERT_KNOWN(TlDValidKnownO_A,    tl_o.d_valid  )
  `ASSERT_KNOWN(TlAReadyKnownO_A,    tl_o.a_ready  )
  `ASSERT_KNOWN(PwrKnownO_A,         pwr_o         )
  `ASSERT_KNOWN(ResetsKnownO_A,      resets_o      )
  `ASSERT_KNOWN(AstResetsKnownO_A, resets_ast_o )

endmodule // rstmgr
