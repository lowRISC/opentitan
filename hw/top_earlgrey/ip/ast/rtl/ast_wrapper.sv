// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is the integration wrapper layer for AST

`include "prim_assert.sv"

module ast_wrapper import ast_wrapper_pkg::*;
(
  // root clock / rests
  input clk_ext_i,
  input por_ni,

  // Bus Interface
  input tlul_pkg::tl_h2d_t bus_i,
  output tlul_pkg::tl_d2h_t bus_o,

  // pwrmgr interface
  input pwrmgr_pkg::pwr_ast_req_t pwr_i,
  output pwrmgr_pkg::pwr_ast_rsp_t pwr_o,

  // rstmgr interface
  output ast_rst_t rst_o,

  // clkmgr interface
  output ast_clks_t clks_o,

  // usb interface
  input usb_ref_pulse_i,
  input usb_ref_val_i,

  // synchronization clocks / rests
  input clkmgr_pkg::clkmgr_ast_out_t clks_ast_i,
  input rstmgr_pkg::rstmgr_ast_out_t rsts_ast_i,

  // adc
  // The adc package definition should eventually be moved to the adc module
  input adc_ast_req_t adc_i,
  output adc_ast_rsp_t adc_o,

  // entropy source interface
  // The entropy source pacakge definition should eventually be moved to es
  input entropy_src_pkg::entropy_src_rng_req_t es_i,
  output entropy_src_pkg::entropy_src_rng_rsp_t es_o,

  // alerts interface
  input ast_alert_rsp_t alert_i,
  output ast_alert_req_t alert_o,

  // assorted ast status
  output ast_status_t status_o,

  // dft related
  input scanmode_i,
  input scan_reset_ni,

  // usb io calibration
  output logic [UsbCalibWidth-1:0] usb_io_pu_cal_o,

  // IO connection to flash
  output ast_eflash_t ast_eflash_o
);

  // For nettype real awire;
  import ana_pkg::*;

  //TODO: Added for new typdef's
  import ast_pkg::*;


  ///////////////////////////
  // AST instantiation
  ///////////////////////////

  // Switch these to prim_mux cells
  logic core_clk_val;
  logic slow_clk_val;
  logic io_clk_val;
  logic usb_clk_val;

  assign pwr_o.core_clk_val = core_clk_val ? pwrmgr_pkg::DiffValid : pwrmgr_pkg::DiffInvalid;
  assign pwr_o.slow_clk_val = slow_clk_val ? pwrmgr_pkg::DiffValid : pwrmgr_pkg::DiffInvalid;
  assign pwr_o.io_clk_val   = io_clk_val   ? pwrmgr_pkg::DiffValid : pwrmgr_pkg::DiffInvalid;
  assign pwr_o.usb_clk_val  = usb_clk_val  ? pwrmgr_pkg::DiffValid : pwrmgr_pkg::DiffInvalid;

// need to hookup later
`ifndef VERILATOR
`ifndef SYNTHESIS
  awire adc_a0_a; // ADC A0 Analog Input
  awire adc_a1_a; // ADC A1 Analog Input
  assign adc_a0_a = 0.0;
  assign adc_a1_a = 0.0;
  awire pad2ast_t0_a; // T0 Analog Input
  awire pad2ast_t1_a; // T1 Analog Input
  assign pad2ast_t0_a = 0.0;
  assign pad2ast_t1_a = 0.0;
`else
  wire adc_a0_a;  // ADC A0 Analog Input
  wire adc_a1_a;  // ADC A1 Analog Input
  assign adc_a0_a = 1'b0;
  assign adc_a1_a = 1'b0;
  wire pad2ast_t0_a; // T0 Analog Input
  wire pad2ast_t1_a; // T1 Analog Input
  assign pad2ast_t0_a = 1'b0;
  assign pad2ast_t1_a = 1'b0;
`endif
`else
  wire adc_a0_a;  // ADC A0 Analog Input
  wire adc_a1_a;  // ADC A1 Analog Input
  assign adc_a0_a = 1'b0;
  assign adc_a1_a = 1'b0;
  wire pad2ast_t0_a; // T0 Analog Input
  wire pad2ast_t1_a; // T1 Analog Input
  assign pad2ast_t0_a = 1'b0;
  assign pad2ast_t1_a = 1'b0;
`endif


  ast #(
    .EntropyStreams(EntropyStreams),
    .AdcChannels(AdcChannels),
    .AdcDataWidth(AdcDataWidth),
    .UsbCalibWidth(UsbCalibWidth)
  ) i_ast (
    // ast interface and sync clocks / rests
    .clk_ast_adc_i(1'b0),  // not yet in design
    .clk_ast_rng_i(1'b0),  // not yet in design
    .clk_ast_usb_i(clks_ast_i.clk_ast_usbdev_usb_peri),
    .clk_ast_es_i(1'b0),   // not yet in design
    // sensor control acts as both the alert interface and the tlul     // front-end
    .clk_ast_alert_i(clks_ast_i.clk_ast_sensor_ctrl_aon_io_div4_secure),
    .clk_ast_tlul_i(clks_ast_i.clk_ast_sensor_ctrl_aon_io_div4_secure),
    .rst_ast_adc_ni(1'b0), // not yet in design
    .rst_ast_rng_ni(1'b0), // not yet in design
    .rst_ast_usb_ni(rsts_ast_i.rst_ast_usbdev_usb_n),
    .rst_ast_es_ni(1'b0),
    .rst_ast_alert_ni(rsts_ast_i.rst_ast_sensor_ctrl_aon_sys_io_div4_n),
    .rst_ast_tlul_ni(rsts_ast_i.rst_ast_sensor_ctrl_aon_sys_io_div4_n),

    // tlul if
    .tl_i(bus_i),
    .tl_o(bus_o),

    // power related
    .por_ni,
    .vcaon_pok_o(rst_o.aon_pok),
    .vcmain_pok_o(pwr_o.main_pok),
    .vioa_pok_o(status_o.io_pok[0]),
    .viob_pok_o(status_o.io_pok[1]),
    .main_pd_ni(pwr_i.main_pd_n),
    .main_iso_en_i(pwr_i.pwr_clamp),

    // power OK control (for debug only). pok signal follows these inputs
    .vcc_supp_i(1'b1),                        // VCC Supply Test
    .vcmain_supp_i(1'b1),                     // MAIN Supply Test
    .vcaon_supp_i(1'b1),                      // AON Supply Test
    .vioa_supp_i(1'b1),                       // IO Rails Supply Test
    .viob_supp_i(1'b1),                       // IO Rails Supply Test

    // output clocks and associated controls
    .clk_src_sys_o(clks_o.clk_sys),
    .clk_src_sys_val_o(core_clk_val),
    .clk_src_sys_en_i(pwr_i.core_clk_en),
    .clk_src_sys_jen_i(1'b0),                 // need to add function in clkmgr

    .clk_src_aon_o(clks_o.clk_aon),
    .clk_src_aon_val_o(slow_clk_val),

    .clk_src_usb_o(clks_o.clk_usb),
    .clk_src_usb_val_o(usb_clk_val),
    .clk_src_usb_en_i(pwr_i.usb_clk_en),

    .clk_src_io_o(clks_o.clk_io),
    .clk_src_io_val_o(io_clk_val),
    .clk_src_io_en_i(pwr_i.io_clk_en),

    // input clock and references for calibration
    .clk_ast_ext_i(clk_ext_i),
    .usb_ref_pulse_i,
    .usb_ref_val_i,

    // ADC interface
    .adc_a0_ai(adc_a0_a),
    .adc_a1_ai(adc_a1_a),
    .adc_chnsel_i(adc_i.channel_sel),
    .adc_pd_i(adc_i.pd),
    .adc_d_o(adc_o.data),
    .adc_d_val_o(adc_o.data_valid),

    // entropy source interface
    .rng_en_i(es_i.rng_enable),
    .rng_val_o(es_o.rng_valid),
    .rng_b_o(es_o.rng_b),

    // entropy distribution interface - need to hookup later
    .entropy_req_o(),
    .entropy_ack_i('0),
    .entropy_i('0),

    // alerts
    .as_alert_po(alert_o.alerts_p[sensor_ctrl_reg_pkg::AsSel]),
    .as_alert_no(alert_o.alerts_n[sensor_ctrl_reg_pkg::AsSel]),
    .cg_alert_po(alert_o.alerts_p[sensor_ctrl_reg_pkg::CgSel]),
    .cg_alert_no(alert_o.alerts_n[sensor_ctrl_reg_pkg::CgSel]),
    .gd_alert_po(alert_o.alerts_p[sensor_ctrl_reg_pkg::GdSel]),
    .gd_alert_no(alert_o.alerts_n[sensor_ctrl_reg_pkg::GdSel]),
    .ts_alert_hi_po(alert_o.alerts_p[sensor_ctrl_reg_pkg::TsHiSel]),
    .ts_alert_hi_no(alert_o.alerts_n[sensor_ctrl_reg_pkg::TsHiSel]),
    .ts_alert_lo_po(alert_o.alerts_p[sensor_ctrl_reg_pkg::TsLoSel]),
    .ts_alert_lo_no(alert_o.alerts_n[sensor_ctrl_reg_pkg::TsLoSel]),
    .ls_alert_po(alert_o.alerts_p[sensor_ctrl_reg_pkg::LsSel]),
    .ls_alert_no(alert_o.alerts_n[sensor_ctrl_reg_pkg::LsSel]),
    .ot_alert_po(alert_o.alerts_p[sensor_ctrl_reg_pkg::OtSel]),
    .ot_alert_no(alert_o.alerts_n[sensor_ctrl_reg_pkg::OtSel]),
    .as_alert_ack_i(alert_i.alerts_ack[sensor_ctrl_reg_pkg::AsSel]),
    .cg_alert_ack_i(alert_i.alerts_ack[sensor_ctrl_reg_pkg::CgSel]),
    .gd_alert_ack_i(alert_i.alerts_ack[sensor_ctrl_reg_pkg::GdSel]),
    .ts_alert_hi_ack_i(alert_i.alerts_ack[sensor_ctrl_reg_pkg::TsHiSel]),
    .ts_alert_lo_ack_i(alert_i.alerts_ack[sensor_ctrl_reg_pkg::TsLoSel]),
    .ls_alert_ack_i(alert_i.alerts_ack[sensor_ctrl_reg_pkg::LsSel]),
    .ot_alert_ack_i(alert_i.alerts_ack[sensor_ctrl_reg_pkg::OtSel]),
    .as_alert_trig_i(alert_i.alerts_trig[sensor_ctrl_reg_pkg::AsSel]),
    .cg_alert_trig_i(alert_i.alerts_trig[sensor_ctrl_reg_pkg::CgSel]),
    .gd_alert_trig_i(alert_i.alerts_trig[sensor_ctrl_reg_pkg::GdSel]),
    .ts_alert_hi_trig_i(alert_i.alerts_trig[sensor_ctrl_reg_pkg::TsHiSel]),
    .ts_alert_lo_trig_i(alert_i.alerts_trig[sensor_ctrl_reg_pkg::TsLoSel]),
    .ls_alert_trig_i(alert_i.alerts_trig[sensor_ctrl_reg_pkg::LsSel]),
    .ot_alert_trig_i(alert_i.alerts_trig[sensor_ctrl_reg_pkg::OtSel]),

    // flash interface
    .flash_power_down_h_o(ast_eflash_o.flash_power_down_h),
    .flash_power_ready_h_o(ast_eflash_o.flash_power_ready_h),

    // analog debug signals
    .ast2pad_a_io(),

    // pad mux related - DFT
    .ast2padmux_o(),  // DFT_2_IO Output Signals
    .padmux2ast_i('0),  // IO_2_DFT Input Signals

    // usb IO calib
    .usb_io_pu_cal_o, // USB IO Pull-up Calibration Setting

    // dft related
    .scan_mode_i(scanmode_i),
    .scan_reset_ni
  );

  // TODO hook-up to ast
  assign ast_eflash_o.flash_bist_enable = lc_ctrl_pkg::Off;

endmodule // ast_wrapper

//lc_ctrl_pkg::lc_tx_t flash_bist_en_o;
//assign ast_eflash_o.flash_bist_enable = (flash_bist_en_o == lc_ctrl_pkg::On);
//
//ast_pkg::ast_dif_t as_alert_o;
//assign alert_o.alerts_p[sensor_ctrl_reg_pkg::AsSel] = as_alert_o.p;
//assign alert_o.alerts_n[sensor_ctrl_reg_pkg::AsSel] = as_alert_o.n;
//
//ast_pkg::ast_dif_t cg_alert_o;
//assign alert_o.alerts_p[sensor_ctrl_reg_pkg::CgSel] = cg_alert_o.p;
//assign alert_o.alerts_n[sensor_ctrl_reg_pkg::CgSel] = cg_alert_o.n;
//
//ast_pkg::ast_dif_t gd_alert_o;
//assign alert_o.alerts_p[sensor_ctrl_reg_pkg::GdSel] = gd_alert_o.p;
//assign alert_o.alerts_n[sensor_ctrl_reg_pkg::GdSel] = gd_alert_o.n;
//
//ast_pkg::ast_dif_t ts_alert_hi_o;
//assign alert_o.alerts_p[sensor_ctrl_reg_pkg::TsHiSel] = ts_alert_hi_o.p;
//assign alert_o.alerts_n[sensor_ctrl_reg_pkg::TsHiSel] = ts_alert_hi_o.n;
//
//ast_pkg::ast_dif_t ts_alert_lo_o;
//assign alert_o.alerts_p[sensor_ctrl_reg_pkg::TsLoSel] = ts_alert_lo_o.p;
//assign alert_o.alerts_n[sensor_ctrl_reg_pkg::TsLoSel] = ts_alert_lo_o.n;
//
//ast_pkg::ast_dif_t ls_alert_o;
//assign alert_o.alerts_p[sensor_ctrl_reg_pkg::LsSel] = ls_alert_o.p;
//assign alert_o.alerts_n[sensor_ctrl_reg_pkg::LsSel] = ls_alert_o.n;
//
//ast_pkg::ast_dif_t ot_alert_o;
//assign alert_o.alerts_p[sensor_ctrl_reg_pkg::OtSel] = ot_alert_o.p;
//assign alert_o.alerts_n[sensor_ctrl_reg_pkg::OtSel] = ot_alert_o.n;
//
////~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//// Module: 'ast' - Jun 25, 2020. 'vinst.pl' Rev 1.06
////~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//ast #(
///*P*/ .EntropyStreams ( EntropyStreams ),
///*P*/ .AdcChannels ( AdcChannels ),
///*P*/ .AdcDataWidth ( AdcDataWidth ),
///*P*/ .UsbCalibWidth ( UsbCalibWidth ),
///*P*/ .Ast2PadOutWidth ( 10 ),                                 //TODO: Assign
///*P*/ .Pad2AstInWidth ( 10 )                                   //TODO: Assign
//) u_ast (
//      // tlul
///*I*/ .tl_i ( bus_i ),
///*O*/ .tl_o ( bus_o ),
//      // buffered clocks & resets
///*I*/ .clk_ast_adc_i ( 1'b0 ),                        // Not yet in the design
///*I*/ .rst_ast_adc_ni ( 1'b0 ),                       // Not yet in the design
///*I*/ .clk_ast_alert_i ( clks_ast_i.clk_ast_sensor_ctrl_io_div4_secure ),
///*I*/ .rst_ast_alert_ni ( rsts_ast_i.rst_ast_sensor_ctrl_sys_io_div4_n ),  //JL TODO
///*I*/ .clk_ast_es_i ( 1'b0 ),                         // Not yet in the design
///*I*/ .rst_ast_es_ni ( 1'b0 ),                        // Not yet in the design
///*I*/ .clk_ast_rng_i ( 1'b0 ),                        // Not yet in the design
///*I*/ .rst_ast_rng_ni ( 1'b0 ),                       // Not yet in the design
///*I*/ .clk_ast_tlul_i ( clks_ast_i.clk_ast_sensor_ctrl_io_div4_secure ),
///*I*/ .rst_ast_tlul_ni ( rsts_ast_i.rst_ast_sensor_ctrl_sys_io_div4_n ),  //JL TODO
///*I*/ .clk_ast_usb_i ( clks_ast_i.clk_ast_usbdev_usb_peri ),
///*I*/ .rst_ast_usb_ni ( rsts_ast_i.rst_ast_usbdev_usb_n ),  //JL TODO
///*I*/ .clk_ast_ext_i ( clk_ext_i ),
///*I*/ .por_ni ( por_ni ),
//      // pok test
///*I*/ .vcc_supp_i ( 1'b1 ),                           // VCC Supply Test
///*I*/ .vcaon_supp_i ( 1'b1 ),                         // AON Supply Test
///*I*/ .vcmain_supp_i ( 1'b1 ),                        // MAIN Supply Test
///*I*/ .vioa_supp_i ( 1'b1 ),                          // IO Rails Supply Test
///*I*/ .viob_supp_i ( 1'b1 ),                          // IO Rails Supply Test
//      // pok
///*O*/ .vcaon_pok_o ( rst_o.aon_pok ),
///*O*/ .vcmain_pok_o ( pwr_o.main_pok ),
///*O*/ .vioa_pok_o ( status_o.io_pok[0] ),
///*O*/ .viob_pok_o ( status_o.io_pok[1] ),
//      // main regulator
///*I*/ .main_iso_en_i ( pwr_i.pwr_clamp ),
///*I*/ .main_pd_ni ( pwr_i.main_pd_n ),
//      // pdm control (flash)/otp
///*O*/ .flash_power_down_h_o ( ast_eflash_o.flash_power_down_h ),
///*O*/ .flash_power_ready_h_o ( ast_eflash_o.flash_power_ready_h ),
///*I*/ .otp_power_seq_i ( 2'b00 ),                             //TODO: Connect
///*O*/ .otp_power_seq_h_o ( ),                                 //TODO: Connect
//      // system source clock
///*I*/ .clk_src_sys_en_i ( pwr_i.core_clk_en ),
///*I*/ .clk_src_sys_jen_i ( 1'b0 ),           // need to add function in clkmgr
///*O*/ .clk_src_sys_o ( clks_o.clk_sys  ),
///*O*/ .clk_src_sys_val_o ( core_clk_val ),
//      // aon source clock
///*O*/ .clk_src_aon_o ( clks_o.clk_aon ),
///*O*/ .clk_src_aon_val_o ( slow_clk_val ),
//      // io source clock
///*I*/ .clk_src_io_en_i ( pwr_i.io_clk_en ),
///*O*/ .clk_src_io_o ( clks_o.clk_io ),
///*O*/ .clk_src_io_val_o ( io_clk_val ),
//      // usb source clock
///*I*/ .usb_ref_pulse_i ( usb_ref_pulse_i ),
///*I*/ .usb_ref_val_i ( usb_ref_val_i ),
///*I*/ .clk_src_usb_en_i ( pwr_i.usb_clk_en ),
///*O*/ .clk_src_usb_o ( clks_o.clk_usb ),
///*O*/ .clk_src_usb_val_o ( usb_clk_val ),
///*O*/ .usb_io_pu_cal_o,                  // USB IO Pull-up Calibration Setting
//      // adc
///*I*/ .adc_pd_i ( adc_i.pd ),
///*I*/ .adc_a0_ai ( adc_a0_a ),
///*I*/ .adc_a1_ai ( adc_a1_a ),
///*I*/ .adc_chnsel_i ( adc_i.channel_sel ),
///*O*/ .adc_d_o ( adc_o.data ),
///*O*/ .adc_d_val_o ( adc_o.data_valid ),
//      // rng
///*I*/ .rng_en_i ( es_i.rng_enable ),
///*O*/ .rng_val_o ( es_o.rng_valid ),
///*O*/ .rng_b_o ( es_o.rng_b ),
//      // entropy
///*I*/ .entropy_rsp_i ( '{edn_ack: 1'b0, edn_fips: 1'b1,  edn_bus: '0} ),
///*O*/ .entropy_req_o ( ),                                     //TODO: Connect
//      // alerts
///*I*/ .as_alert_trig_i ( '{ p: 1'b0, n: 1'b1 } ),             //TODO: Connect
///*I*/ .as_alert_ack_i ( '{ p: 1'b0, n: 1'b1 } ),              //TODO: Connect
///*O*/ .as_alert_o ( as_alert_o ),
///*I*/ .cg_alert_trig_i ( '{ p: 1'b0, n: 1'b1 } ),             //TODO: Connect
///*I*/ .cg_alert_ack_i ( '{ p: 1'b0, n: 1'b1 } ),              //TODO: Connect
///*O*/ .cg_alert_o ( cg_alert_o ),
///*I*/ .gd_alert_trig_i ( '{ p: 1'b0, n: 1'b1 } ),             //TODO: Connect
///*I*/ .gd_alert_ack_i ( '{ p: 1'b0, n: 1'b1 } ),              //TODO: Connect
///*O*/ .gd_alert_o ( gd_alert_o ),
///*I*/ .ts_alert_hi_trig_i ( '{ p: 1'b0, n: 1'b1 } ),          //TODO: Connect
///*I*/ .ts_alert_hi_ack_i ( '{ p: 1'b0, n: 1'b1 } ),           //TODO: Connect
///*O*/ .ts_alert_hi_o ( ts_alert_hi_o ),
///*I*/ .ts_alert_lo_trig_i ( '{ p: 1'b0, n: 1'b1 } ),          //TODO: Connect
///*I*/ .ts_alert_lo_ack_i ( '{ p: 1'b0, n: 1'b1 } ),           //TODO: Connect
///*O*/ .ts_alert_lo_o ( ts_alert_lo_o ),
///*I*/ .ls_alert_trig_i ( '{ p: 1'b0, n: 1'b1 } ),             //TODO: Connect
///*I*/ .ls_alert_ack_i ( '{ p: 1'b0, n: 1'b1 } ),              //TODO: Connect
///*O*/ .ls_alert_o ( ls_alert_o ),
///*I*/ .ot_alert_trig_i ( '{ p: 1'b0, n: 1'b1 } ),             //TODO: Connect
///*I*/ .ot_alert_ack_i ( '{ p: 1'b0, n: 1'b1 } ),              //TODO: Connect
///*O*/ .ot_alert_o ( ot_alert_o ),
//      // dft
///*I*/ .dft_strap_test_i ( '{valid: 1'b0, straps: 2'b00} ),    //TODO: Connect
///*I*/ .lc_dft_en_i ( lc_ctrl_pkg::On ),                       //TODO: Connect
//      // pad mux related
///*I*/ .padmux2ast_i ( '0 ),                                   //TODO: Connect
///*O*/ .ast2padmux_o ( ),                                      //TODO: Connect
///*I*/ .pad2ast_t0_ai ( pad2ast_t0_a ),                        //TODO: Connect
///*I*/ .pad2ast_t1_ai ( pad2ast_t1_a  ),                       //TODO: Connect
///*O*/ .ast2pad_t0_ao ( ),                                     //TODO: Connect
///*O*/ .ast2pad_t1_ao ( ),                                     //TODO: Connect
//      //
///*I*/ .lc_clk_byp_req_i ( lc_ctrl_pkg::Off ),                 //TODO: Connect
///*O*/ .lc_clk_byp_ack_o ( ),                                  //TODO: Connect
///*O*/ .flash_bist_en_o ( flash_bist_en_o ),                   //TODO: Connect
//      //
///*O*/ .dpram_rmf_o ( ),                                       //TODO: Connect
///*O*/ .dpram_rml_o ( ),                                       //TODO: Connect
///*O*/ .spram_rm_o ( ),                                        //TODO: Connect
///*O*/ .sprgf_rm_o ( ),                                        //TODO: Connect
///*O*/ .sprom_rm_o ( ),                                        //TODO: Connect
//      // scan
///*O*/ .dft_scan_md_o ( ),                                     //TODO: Connect
///*O*/ .scan_shift_en_o ( ),                                   //TODO: Connect
///*O*/ .scan_reset_no ( )                                      //TODO: Connect
//);
//// end of u_ast
//
//
//
//endmodule : ast_wrapper
//>>>>>>> 05149b668 ([ast] Added DFT interface + logic updates)
