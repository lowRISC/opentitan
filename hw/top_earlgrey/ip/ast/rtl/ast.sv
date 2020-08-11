// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: ast
// *Module Description: Analog Sensors Top
//
//############################################################################
`timescale 1ns / 1ps

module ast #(
    parameter int EntropyStreams = 4,
    parameter int EntropyInWidth = 1,
    parameter int AdcChannels = 2,
    parameter int AdcDataWidth = 10,
    parameter int Ast2PadOutWidth = 16,  // TBD
    parameter int Pad2AstInWidth = 16,  // TBD
    parameter int JitCalibWidth = 16,  // TBD
    parameter int JitSRateWidth = 16,  // TBD
    parameter int UsbCalibWidth = 16  // TBD
) (
    // Power and IO pin connections
    input main_iso_en_i,  // Isolation enable for main core power (VCMAIN).

    // tlul if
    input  tlul_pkg::tl_h2d_t tl_i,  // TLUL H2D
    output tlul_pkg::tl_d2h_t tl_o,  // TLUL D2H

    // clocks / rests
    input clk_ast_adc_i,  // Buffered AST ADC Clock
    input rst_ast_adc_ni,  // Buffered AST ADC Reset
    input clk_ast_alert_i,  // Buffered AST Alert Clock
    input rst_ast_alert_ni,  // Buffered AST Alert Reset
    input clk_ast_es_i,  // Buffered AST Entropy Source Clock
    input rst_ast_es_ni,  // Buffered AST Entropy Source Reset
    input clk_ast_rng_i,  // Buffered AST RNG Clock
    input rst_ast_rng_ni,  // Buffered AST RNG Reset
    input clk_ast_tlul_i,  // Buffered AST TLUL Clock
    input rst_ast_tlul_ni,  // Buffered AST TLUL Reset
    input clk_ast_usb_i,  // Buffered AST USB Clock
    input rst_ast_usb_ni,  // Buffered AST USB Reset
    input clk_ast_ext_i,  // Buffered AST External Clock
    input por_ni,  // Power ON Reset

    // power OK control
    // In non-power aware DV environment, the <>_supp_i is for debug only!
    // POK signal follow this input.
    // In a power aware environment this signal should be connected to constant '1'
    input        vcc_supp_i,  // VCC Supply Test
    input        vcaon_supp_i,  // VCAON Supply Test
    input        vcmain_supp_i,  // VCMAIN Supply Test
    input        vioa_supp_i,  // VIOA Rail Supply Test
    input        viob_supp_i,  // VIOB Rail Supply Test
    output logic vcaon_pok_o,  // VCAON Power OK
    output logic vcmain_pok_o,  // VCMAIN Power OK
    output logic vioa_pok_o,  // VIOA Rail Power OK
    output logic viob_pok_o,  // VIOB Rail Power OK

    // main regulator
    input main_pd_ni,  // MAIN Regulator Power Down

    // power down monitor logic - flash related
    output logic flash_power_down_h_o,  // Flash Power Down
    output logic flash_power_ready_h_o,  // Flash Power Ready

    // system source clock
    input        clk_src_sys_en_i,  // SYS Source Clock Enable
    input        clk_src_sys_jen_i,  // SYS Source Clock Jitter Enable
    output logic clk_src_sys_o,  // SYS Source Clock
    output logic clk_src_sys_val_o,  // SYS Source Clock Valid

    // aon source clock
    output logic clk_src_aon_o,  // AON Source Clock
    output logic clk_src_aon_val_o,  // AON Source Clock Valid

    // io source clock
    input        clk_src_io_en_i,  // IO Source Clock Enable
    output logic clk_src_io_o,  // IO Source Clock
    output logic clk_src_io_val_o,  // IO Source Clock Valid

    // usb source clock
    input                            usb_ref_pulse_i,  // USB Reference Pulse
    input                            usb_ref_val_i,  // USB Reference Valid
    input                            clk_src_usb_en_i,  // USB Source Clock Enable
    output logic                     clk_src_usb_o,  // USB Source Clock
    output logic                     clk_src_usb_val_o,  // USB Source Clock Valid
    output logic [UsbCalibWidth-1:0] usb_io_pu_cal_o,  // USB IO Pull-up Calibration Setting

    // adc interface
    input                     adc_pd_i,  // ADC Power Down
    input  [ AdcChannels-1:0] adc_ai,  // ADC Analog (per channel)
    input  [ AdcChannels-1:0] adc_chnsel_i,  // ADC Channel Select
    output [AdcDataWidth-1:0] adc_d_o,  // ADC Digital (per channel)
    output                    adc_d_val_o,  // ADC Digital Valid

    // entropy source interface
    input                             rng_en_i,  // RNG Enable
    output logic                      rng_ok_o,  // RNG OK
    output logic [EntropyStreams-1:0] rng_b_o,  // RNG Bit(s)

    // entropy distribution interface
    input                             entropy_ack_i,  // Entropy Acknowlage
    input        [EntropyInWidth-1:0] entropy_i,  // Entropy
    output logic                      entropy_req_o,  // Entropy Request

    // alerts
    input        as_alert_trig_i,  // Active Shield Alert Trigger
    input        as_alert_ack_i,  // Active Shield Alert Acknowlage
    output logic as_alert_po,  // Active Shield Alert Positive
    output logic as_alert_no,  // Active Shield Alert Negative

    input        cg_alert_trig_i,  // CG Alert Trigger
    input        cg_alert_ack_i,  // CG Alert Acknowlage
    output logic cg_alert_po,  // CG Alert Positive
    output logic cg_alert_no,  // CG Alert Negative

    input        gd_alert_trig_i,  // GD Alert Trigger
    input        gd_alert_ack_i,  // GD Alert Acknowlage
    output logic gd_alert_po,  // GD Alert Positive
    output logic gd_alert_no,  // GD Alert Negative

    input        ts_alert_hi_trig_i,  // TS High Alert Trigger
    input        ts_alert_hi_ack_i,  // TS High Alert Acknowlage
    output logic ts_alert_hi_po,  // TS High Alert Positive
    output logic ts_alert_hi_no,  // TS High Alert Negative

    input        ts_alert_lo_trig_i,  // TS Low Alert Trigger
    input        ts_alert_lo_ack_i,  // TS Low Alert Acknowlage
    output logic ts_alert_lo_po,  // TS Low Alert Positive
    output logic ts_alert_lo_no,  // TS Low Alert Negative

    input        ls_alert_trig_i,  // LS Alert Trigger
    input        ls_alert_ack_i,  // LS Alert Acknowlage
    output logic ls_alert_po,  // LS Alert Positive
    output logic ls_alert_no,  // LS Alert Negative

    input        ot_alert_trig_i,  // OT Alert Trigger
    input        ot_alert_ack_i,  // OT Alert Acknowlage
    output logic ot_alert_po,  // OT Alert Positive
    output logic ot_alert_no,  // OT Alert Negative

    // pad mux related - DFT
    input        [ Pad2AstInWidth-1:0] padmux2ast_i,  // IO_2_DFT Input Signals
    output logic [Ast2PadOutWidth-1:0] ast2padmux_o,  // DFT_2_IO Output Signals
    inout  wire                        ast2pad_a_io,  // TODO: If needed, add width param

    // Scan
    input scan_mode_i,  // Scan Mode
    input scan_reset_ni  // Scan Reset
);

  import ast_reg_pkg::*;

  // To HW
  /*O*/ ast_reg_pkg::ast_reg2hw_t reg2hw;  // Write

  logic vcaon_pok, vcaon_pok_h;



  /////////////////////////////////
  // Power OK
  /////////////////////////////////
  // Local signals for testing hook
  logic vcc_a;
  assign vcc_a = 1'b1;
  logic vioa_a;
  assign vioa_a = 1'b1;
  logic viob_a;
  assign viob_a = 1'b1;
  logic vcaon_a;
  assign vcaon_a = 1'b1;
  logic vcmain_a;
  assign vcmain_a = 1'b1;

  logic vcc_pok_h, vcc_pok;

  // VCC POK
  gen_pok #(
      // synopsys translate_off
      /*P*/.POK_RDLY(3us),
      /*P*/.POK_FDLY(500ns)
  // synopsys translate_on
  ) i_vcc_pok (
      /*I*/.gen_supp_a(vcc_a),
      /*I*/.gen_supp_i(vcc_supp_i),
      /*O*/.gen_pok_o (vcc_pok_h)
  );

  assign vcc_pok = vcc_pok_h;  // "Level Shifter"

  logic vcmain_pok, vcmain_pok_h;


  // VCAON POK
  gen_pok #(
      // synopsys translate_off
      /*P*/.POK_RDLY(3us),
      /*P*/.POK_FDLY(500ns)
  // synopsys translate_on
  ) i_vcaon_pok (
      /*I*/.gen_supp_a(vcaon_a),
      /*I*/.gen_supp_i(vcaon_supp_i),
      /*O*/.gen_pok_o (vcaon_pok)
  );

  // 'por_sync_n' reset deasetion synchronizer output
  logic por_syn_rst_n, por_sync0_n, por_sync_n;

  assign por_syn_rst_n = por_ni && vcc_pok && vcaon_pok;

  always_ff @(posedge clk_src_aon_o, negedge por_syn_rst_n) begin
    if (!por_syn_rst_n) begin
      por_sync0_n <= 1'b0;
      por_sync_n <= 1'b0;
    end else begin
      por_sync0_n <= 1'b1;
      por_sync_n <= por_sync0_n;
    end
  end

  assign vcaon_pok_o = por_sync_n && vcc_pok && vcaon_pok;


  // VCMAIN POK

  // Power up/down with rise/fall delays.
  logic main_pwr_dly;

  gen_pok #(
      // synopsys translate_off
      /*P*/.POK_RDLY(3us),
      /*P*/.POK_FDLY(500ns)
  // synopsys translate_on
  ) i_vcmain_pok (
      /*I*/.gen_supp_a(vcmain_a && main_pwr_dly),
      /*I*/.gen_supp_i(vcmain_supp_i),
      /*O*/.gen_pok_o (vcmain_pok)
  );

  assign vcmain_pok_o = vcaon_pok_o && vcmain_pok;


  // VIOA POK
  logic vioa_pok;

  gen_pok #(
      // synopsys translate_off
      /*P*/.POK_RDLY(3us),
      /*P*/.POK_FDLY(500ns)
  // synopsys translate_on
  ) i_vioa_pok (
      /*I*/.gen_supp_a(vioa_a),
      /*I*/.gen_supp_i(vioa_supp_i),
      /*O*/.gen_pok_o (vioa_pok)
  );

  assign vioa_pok_o = vcaon_pok && vioa_pok;


  // VIOB POK
  logic viob_pok;

  gen_pok #(
      // synopsys translate_off
      /*P*/.POK_RDLY(3us),
      /*P*/.POK_FDLY(500ns)
  // synopsys translate_on
  ) i_viob_pok (
      /*I*/.gen_supp_a(viob_a),
      /*I*/.gen_supp_i(viob_supp_i),
      /*O*/.gen_pok_o (viob_pok)
  );

  assign viob_pok_o = vcaon_pok && viob_pok;


  /////////////////////////////////
  // Main Regulator
  /////////////////////////////////

  // Main Regulator (VCC)
  main_rglt #(
      // synopsys translate_off
      /*P*/.MRVCC_RDLY(5us),
      /*P*/.MRVCC_FDLY(100ns),
      /*P*/.MRPD_RDLY(50us),
      /*P*/.MRPD_FDLY(1us)
  // synopsys translate_on
  ) i_main_rglt (
      /*I*/.vcc_pok_i   (vcc_pok),
      /*I*/.main_pd_ni  (main_pd_ni),
      /*O*/.main_pwr_dly(main_pwr_dly)
  );


  /////////////////////////////////
  // PDM (Power Down Mode) Logic
  /////////////////////////////////

  // Power Down Mode (VCC)
  pdm i_pdm (
      /*I*/.vcc_pok_i            (vcc_pok_h),
      /*I*/.vcmain_pok_i         (vcmain_pok),
      /*I*/.main_pd_ni           (main_pd_ni),
      /*O*/.flash_power_down_h_o (flash_power_down_h_o),
      /*O*/.flash_power_ready_h_o(flash_power_ready_h_o)
  );


  /////////////////////////////////
  // Clocking
  /////////////////////////////////

  // System Clock (Always ON)
  sys_clk #(
      // synopsys translate_off
      /*P*/.SYS_EN_RDLY(10us),
      /*P*/.SYS_EN_FDLY(100ns),
      /*P*/.SYS_JEN_RDLY(80ns),
      /*P*/.SYS_JEN_FDLY(80ns)
  // synopsys translate_on
  ) i_sys_clk (
      /*I*/.clk_src_sys_en_i (clk_src_sys_en_i),
      /*I*/.clk_src_sys_jen_i(clk_src_sys_jen_i),
      /*I*/.rst_ni           (vcmain_pok_o),
      /*O*/.clk_src_sys_o    (clk_src_sys_o),
      /*O*/.clk_src_sys_val_o(clk_src_sys_val_o)
  );

  // USB Clock (Always ON)
  usb_clk #(
      // synopsys translate_off
      /*P*/.USB_EN_RDLY(10us),
      /*P*/.USB_EN_FDLY(100ns),
      /*P*/.USB_VAL_RDLY(80ns),  // Reduced for simulation from 50ms
      /*P*/.USB_VAL_FDLY(80ns),
      // synopsys translate_on
      /*P*/.UsbCalibWidth(UsbCalibWidth)
  ) i_usb_clk (
      /*I*/.rst_ni           (vcmain_pok_o),
      /*I*/.clk_src_usb_en_i (clk_src_usb_en_i),
      /*I*/.usb_ref_pulse_i  (usb_ref_pulse_i),
      /*I*/.usb_ref_val_i    (usb_ref_val_i),
      /*O*/.clk_src_usb_o    (clk_src_usb_o),
      /*O*/.clk_src_usb_val_o(clk_src_usb_val_o)
  );

  // AON Clock (Always ON)
  aon_clk #(
      // synopsys translate_off
      /*P*/.AON_EN_RDLY(10us),
      /*P*/.AON_EN_FDLY(100ns)
  // synopsys translate_on
  ) i_aon_clk (
      /*I*/.rst_ni           (vcaon_pok),
      /*O*/.clk_src_aon_o    (clk_src_aon_o),
      /*O*/.clk_src_aon_val_o(clk_src_aon_val_o)
  );

  // IO Clock (Always ON)
  io_clk #(
      // synopsys translate_off
      /*P*/.IO_EN_RDLY(10us),
      /*P*/.IO_EN_FDLY(100ns)
  // synopsys translate_on
  ) i_io_clk (
      /*O*/.clk_src_io_o    (clk_src_io_o),
      /*O*/.clk_src_io_val_o(clk_src_io_val_o),
      /*I*/.clk_src_io_en_i (clk_src_io_en_i),
      /*I*/.rst_ni          (vcmain_pok_o)
  );


  /////////////////////////////////
  // ADC
  /////////////////////////////////

  // ADC (Always ON)
  adc #(
      /*P*/.AdcDataWidth(AdcDataWidth),
      /*P*/.AdcChannels(AdcChannels),
      /*P*/.AdcCnvtClks(44)
  ) i_adc (
      /*I*/.adc_ai      (adc_ai[AdcChannels - 1:0]),
      /*I*/.adc_chnsel_i(adc_chnsel_i[AdcChannels - 1:0]),
      /*I*/.adc_pd_i    (adc_pd_i),
      /*I*/.clk_adc_i   (clk_ast_adc_i),
      /*I*/.rst_adc_ni  (rst_ast_adc_ni),
      /*O*/.adc_d_o     (adc_d_o[AdcDataWidth - 1:0]),
      /*O*/.adc_d_val_o (adc_d_val_o)
  );


  /////////////////////////////////
  // ENTROPY & RNG
  /////////////////////////////////

  // Entropy (Always ON)
  localparam int EntropyRateWidth = 4;
  logic [EntropyRateWidth-1:0] entropy_rate_i;

  entropy #(
      /*P*/.EntropyInWidth(EntropyInWidth),
      /*P*/.EntropyRateWidth(EntropyRateWidth)
  ) i_entropy (
      /*I*/.entropy_ack_i    (entropy_ack_i),
      /*I*/.entropy_i        (entropy_i[EntropyInWidth - 1:0]),
      /*I*/.entropy_rate_i   (entropy_rate_i[EntropyRateWidth - 1:0]),
      /*I*/.clk_src_sys_jen_i(clk_src_sys_jen_i),
      /*I*/.clk_ast_es_i     (clk_ast_es_i),
      /*I*/.rst_ast_es_ni    (rst_ast_es_ni),
      /*I*/.clk_src_sys_i    (clk_src_sys_o),
      /*I*/.rst_src_sys_ni   (vcmain_pok_o),
      /*I*/.scan_mode_i      (scan_mode_i),
      /*O*/.entropy_req_o    (entropy_req_o)
  );

  // RNG (Always ON)
  rng #(
      /*P*/.EntropyStreams(EntropyStreams)
  ) i_rng (
      /*O*/.rng_ok_o(rng_ok_o),
      /*O*/.rng_b_o (rng_b_o[EntropyStreams - 1:0]),
      /*I*/.rng_en_i(rng_en_i),
      /*I*/.clk_i   (clk_ast_rng_i),
      /*I*/.rst_ni  (rst_ast_rng_ni)
  );


  //////////////////////////////////
  // Alerts (Always ON)
  /////////////////////////////////
  // Local signals for testing hook
  logic as_alert_i;
  assign as_alert_i = 1'b0;
  logic cg_alert_i;
  assign cg_alert_i = 1'b0;
  logic gd_alert_i;
  assign gd_alert_i = 1'b0;
  logic ts_alert_hi_i;
  assign ts_alert_hi_i = 1'b0;
  logic ts_alert_lo_i;
  assign ts_alert_lo_i = 1'b0;
  logic ls_alert_i;
  assign ls_alert_i = 1'b0;
  logic ot_alert_i;
  assign ot_alert_i = 1'b0;

  // Active Shield (AS)
  gen_alert i_as_alert (
      /*I*/.gen_alert_i     (as_alert_i),
      /*I*/.gen_alert_trig_i(as_alert_trig_i),
      /*I*/.gen_alert_ack_i (as_alert_ack_i),
      /*I*/.clk_i           (clk_ast_alert_i),
      /*I*/.rst_ni          (rst_ast_alert_ni),
      /*O*/.gen_alert_po    (as_alert_po),
      /*O*/.gen_alert_no    (as_alert_no)
  );

  // Clock Glitch (CG)
  gen_alert i_cg_alert (
      /*I*/.gen_alert_i     (cg_alert_i),
      /*I*/.gen_alert_trig_i(cg_alert_trig_i),
      /*I*/.gen_alert_ack_i (cg_alert_ack_i),
      /*I*/.clk_i           (clk_ast_alert_i),
      /*I*/.rst_ni          (rst_ast_alert_ni),
      /*O*/.gen_alert_po    (cg_alert_po),
      /*O*/.gen_alert_no    (cg_alert_no)
  );

  // Glitch Detector (GD)
  gen_alert i_gd_alert (
      /*I*/.gen_alert_i     (gd_alert_i),
      /*I*/.gen_alert_trig_i(gd_alert_trig_i),
      /*I*/.gen_alert_ack_i (gd_alert_ack_i),
      /*I*/.clk_i           (clk_ast_alert_i),
      /*I*/.rst_ni          (rst_ast_alert_ni),
      /*O*/.gen_alert_po    (gd_alert_po),
      /*O*/.gen_alert_no    (gd_alert_no)
  );

  // Temprature Sensor High (TS Hi)
  gen_alert i_ts_alert_hi (
      /*I*/.gen_alert_i     (ts_alert_hi_i),
      /*I*/.gen_alert_trig_i(ts_alert_hi_trig_i),
      /*I*/.gen_alert_ack_i (ts_alert_hi_ack_i),
      /*I*/.clk_i           (clk_ast_alert_i),
      /*I*/.rst_ni          (rst_ast_alert_ni),
      /*O*/.gen_alert_po    (ts_alert_hi_po),
      /*O*/.gen_alert_no    (ts_alert_hi_no)
  );

  // Temprature Sensor Low (TS Lo)
  gen_alert i_ts_alert_lo (
      /*I*/.gen_alert_i     (ts_alert_lo_i),
      /*I*/.gen_alert_trig_i(ts_alert_lo_trig_i),
      /*I*/.gen_alert_ack_i (ts_alert_lo_ack_i),
      /*I*/.clk_i           (clk_ast_alert_i),
      /*I*/.rst_ni          (rst_ast_alert_ni),
      /*O*/.gen_alert_po    (ts_alert_lo_po),
      /*O*/.gen_alert_no    (ts_alert_lo_no)
  );

  // Light Sensor (LS)
  gen_alert i_ls_alert (
      /*I*/.gen_alert_i     (ls_alert_i),
      /*I*/.gen_alert_trig_i(ls_alert_trig_i),
      /*I*/.gen_alert_ack_i (ls_alert_ack_i),
      /*I*/.clk_i           (clk_ast_alert_i),
      /*I*/.rst_ni          (rst_ast_alert_ni),
      /*O*/.gen_alert_po    (ls_alert_po),
      /*O*/.gen_alert_no    (ls_alert_no)
  );

  // Other Alert (OT)
  gen_alert i_ot_alert (
      /*I*/.gen_alert_i     (ot_alert_i),
      /*I*/.gen_alert_trig_i(ot_alert_trig_i),
      /*I*/.gen_alert_ack_i (ot_alert_ack_i),
      /*I*/.clk_i           (clk_ast_alert_i),
      /*I*/.rst_ni          (rst_ast_alert_ni),
      /*O*/.gen_alert_po    (ot_alert_po),
      /*O*/.gen_alert_no    (ot_alert_no)
  );


  /////////////////////////////////
  // AST Registers Top
  /////////////////////////////////

  // AST REGs (Always ON)
  ast_reg_top i_ast_reg_top (
      /*I*/.clk_i    (clk_ast_tlul_i),
      /*I*/.rst_ni   (rst_ast_tlul_ni),
      /*I*/.tl_i     (tl_i),
      /*O*/.tl_o     (tl_o),
      /*O*/.reg2hw   (reg2hw),
      /*I*/.devmode_i(1'b0)
  );

  // Register output to AST
  logic [32-1:0] ast_rwtype0_q;
  logic [11-1:0] ast_rwtype1_q;

  assign ast_rwtype0_q = reg2hw.rwtype0.q;
  assign ast_rwtype1_q = {
    reg2hw.rwtype1.field15_8.q,
    reg2hw.rwtype1.field4.q,
    reg2hw.rwtype1.field1.q,
    reg2hw.rwtype1.field0.q
  };

  // TODO: Temporrary outputs assignment
  assign entropy_rate_i = 4'd5;
  assign ast2padmux_o = {Ast2PadOutWidth{1'b0}};  // DFT from AST Analog/Digital
  assign usb_io_pu_cal_o = {UsbCalibWidth{1'b0}};  // From AST Regfile


endmodule  // of ast
