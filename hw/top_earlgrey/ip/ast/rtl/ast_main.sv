// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Created for AST domain separation - Main Domain
//
//############################################################################
// *Name: ast_main
// *Module Description: Analog Sensors Top - Main Domain
//############################################################################

`include "prim_assert.sv"

module ast_main (
  // TLUL interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,
  input clk_ast_tlul_i,
  input rst_ast_tlul_ni,
  output prim_mubi_pkg::mubi4_t ast_init_done_o,
  // RNG interface
  input rng_en_i,
  input rng_fips_i,
  output logic rng_val_o,
  output logic [ast_pkg::EntropyStreams-1:0] rng_b_o,
  // Entropy interface
  input edn_pkg::edn_rsp_t entropy_rsp_i,
  output edn_pkg::edn_req_t entropy_req_o,
  // Entropy source clock/reset
  input logic clk_ast_es_i,
  input logic rst_ast_es_ni,
  input prim_mubi_pkg::mubi4_t clk_src_sys_jen_i,
  // Inter-domain communication
  input ast_aon_main_pkg::aon_to_main_t aon_to_main_i,
  output ast_aon_main_pkg::main_to_aon_t main_to_aon_o,
  // Clock bypass interface
  input  logic clk_ast_ext_i,
  input  logic clk_src_sys_en_i,
  input  logic clk_src_io_en_i,
  input  logic clk_src_usb_en_i,
  input  logic clk_ast_usb_i,                      // Buffered AST USB Clock
  input  logic rst_ast_usb_ni,                     // Buffered AST USB Reset
  input  prim_mubi_pkg::mubi4_t io_clk_byp_req_i,
  input  prim_mubi_pkg::mubi4_t all_clk_byp_req_i,
  input  prim_mubi_pkg::mubi4_t ext_freq_is_96m_i,

`ifdef AST_BYPASS_CLK
  // Clocks' Oschillator bypass for OS FPGA
  input ast_pkg::clks_osc_byp_t clk_osc_byp_i,  // Clocks' Oschillator bypass for OS FPGA/VERILATOR
`endif

  // Clock outputs
  output logic clk_src_sys_o,
  output logic clk_src_sys_val_o,
  output logic clk_src_io_o,
  output logic clk_src_io_val_o,
  output prim_mubi_pkg::mubi4_t clk_src_io_48m_o,
  output logic clk_src_usb_o,
  output logic clk_src_usb_val_o,
  output prim_mubi_pkg::mubi4_t io_clk_byp_ack_o,
  output prim_mubi_pkg::mubi4_t all_clk_byp_ack_o,
  // Alert source (TLUL integrity error - passed through from AON for OS)
  output ast_pkg::ast_dif_t ot0_alert_src_o
);

import ast_pkg::* ;
import ast_aon_main_pkg::* ;

///////////////////////////////////////
// TLUL Register Interface
///////////////////////////////////////
ast_reg_pkg::ast_reg2hw_t reg2hw;
ast_reg_pkg::ast_hw2reg_t hw2reg;
logic intg_err;

ast_reg_top u_reg (
  .clk_i ( clk_ast_tlul_i ),
  .rst_ni ( rst_ast_tlul_ni ),
  .tl_i ( tl_i ),
  .tl_o ( tl_o ),
  .reg2hw ( reg2hw ),
  .hw2reg ( hw2reg ),
  .intg_err_o ( intg_err )
);

// Reset and Power-Down for clock modules
logic rst_sys_clk_n, rst_io_clk_n, rst_usb_clk_n;
logic clk_sys_pd_n, clk_io_pd_n, clk_usb_pd_n;

assign rst_sys_clk_n = aon_to_main_i.pwr.vcmain_pok_por && aon_to_main_i.pwr.vcc_pok;
assign rst_io_clk_n  = aon_to_main_i.pwr.vcmain_pok_por && aon_to_main_i.pwr.vcc_pok;
assign rst_usb_clk_n = aon_to_main_i.pwr.vcmain_pok_por && aon_to_main_i.pwr.vcc_pok;

assign clk_sys_pd_n = aon_to_main_i.scan_mode || !aon_to_main_i.clk_osc.deep_sleep;
assign clk_io_pd_n  = aon_to_main_i.scan_mode || !aon_to_main_i.clk_osc.deep_sleep;
assign clk_usb_pd_n = aon_to_main_i.scan_mode || !aon_to_main_i.clk_osc.deep_sleep;

logic clk_sys;

// Local (AST) System clock buffer
////////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_sys_buf (
  .clk_i ( clk_src_sys_o ),
  .clk_o ( clk_sys )
);

logic vcmain_pok_por_sys, rst_src_sys_n;

// Reset De-Assert Sync
prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_sys_dasrt (
  .clk_i ( clk_sys ),
  .rst_ni ( aon_to_main_i.pwr.vcmain_pok_por ),
  .d_i ( 1'b1 ),
  .q_o ( vcmain_pok_por_sys )
);

assign rst_src_sys_n = aon_to_main_i.scan_mode ? aon_to_main_i.scan_reset_n : vcmain_pok_por_sys;


///////////////////////////////////////
// Inter-domain Interface Unpacking
///////////////////////////////////////
ast_aon_main_pkg::clks_byp_aon_to_main_t clks_byp_aon_to_main;
assign clks_byp_aon_to_main = aon_to_main_i.clks_byp;

///////////////////////////////////////
// REGAL Register
///////////////////////////////////////
logic regal_rst_n;
assign regal_rst_n = rst_ast_tlul_ni;

logic regal_we;
logic [32-1:0] regal, regal_di;

assign regal_we = reg2hw.regal.qe;
assign regal_di = reg2hw.regal.q;
assign hw2reg.regal.d = regal;

// REGAL & AST init done indication
always_ff @( posedge clk_ast_tlul_i, negedge regal_rst_n ) begin
  if ( !regal_rst_n ) begin
    regal           <= ast_reg_pkg::AST_REGAL_RESVAL;
    ast_init_done_o <= prim_mubi_pkg::MuBi4False;
  end else if ( regal_we ) begin
    regal           <= regal_di;
    ast_init_done_o <= prim_mubi_pkg::MuBi4True;
  end
end

///////////////////////////////////////
// Main Domain Oscillators (SYS, IO, USB) - OS simplified
///////////////////////////////////////
logic clk_osc_sys;
logic clk_osc_io;
logic clk_osc_usb;
logic clk_osc_sys_val, clk_osc_io_val, clk_osc_usb_val;


`ifdef AST_BYPASS_CLK
logic clk_sys_ext;
assign clk_sys_ext = clk_osc_byp_i.sys;
`endif

sys_clk u_sys_clk (
  .clk_src_sys_jen_i ( prim_mubi_pkg::mubi4_test_true_loose(clk_src_sys_jen_i) ),
  .clk_src_sys_en_i ( clk_src_sys_en_i ),
  .clk_sys_pd_ni ( clk_sys_pd_n ),
  .rst_sys_clk_ni ( rst_sys_clk_n ),
  .vcore_pok_h_i ( aon_to_main_i.pwr.vcmain_pok_h ),
  .scan_mode_i ( aon_to_main_i.scan_mode ),
  .sys_osc_cal_i ( aon_to_main_i.sys_io_osc_cal ),
`ifdef AST_BYPASS_CLK
  .clk_sys_ext_i ( clk_sys_ext ),
`endif
  .clk_src_sys_o ( clk_osc_sys ),
  .clk_src_sys_val_o ( clk_osc_sys_val )
);

`ifdef AST_BYPASS_CLK
logic clk_io_ext;
assign clk_io_ext = clk_osc_byp_i.io;
`endif

io_clk u_io_clk (
  .vcore_pok_h_i ( aon_to_main_i.pwr.vcmain_pok_h ),
  .clk_io_pd_ni ( clk_io_pd_n ),
  .rst_io_clk_ni ( rst_io_clk_n ),
  .clk_src_io_en_i ( clk_src_io_en_i ),
  .scan_mode_i ( aon_to_main_i.scan_mode ),
  .io_osc_cal_i ( aon_to_main_i.sys_io_osc_cal ),
`ifdef AST_BYPASS_CLK
  .clk_io_ext_i ( clk_io_ext ),
`endif
  .clk_src_io_o ( clk_osc_io ),
  .clk_src_io_val_o ( clk_osc_io_val )
);

`ifdef AST_BYPASS_CLK
logic clk_usb_ext;
assign clk_usb_ext = clk_osc_byp_i.usb;
`endif

usb_clk u_usb_clk (
  .vcore_pok_h_i ( aon_to_main_i.pwr.vcmain_pok_h ),
  .clk_usb_pd_ni ( clk_usb_pd_n ),
  .rst_usb_clk_ni ( rst_usb_clk_n ),
  .clk_src_usb_en_i ( clk_src_usb_en_i ),
  .usb_ref_val_i ( aon_to_main_i.clk_osc.usb_ref_val ),
  .usb_ref_pulse_i ( aon_to_main_i.clk_osc.usb_ref_pulse ),
  .clk_ast_usb_i ( clk_ast_usb_i ),
  .rst_ast_usb_ni ( rst_ast_usb_ni ),
  .scan_mode_i ( aon_to_main_i.scan_mode ),
  .usb_osc_cal_i ( aon_to_main_i.usb_osc_cal ),
`ifdef AST_BYPASS_CLK
  .clk_usb_ext_i ( clk_usb_ext ),
`endif
  .clk_src_usb_o ( clk_osc_usb ),
  .clk_src_usb_val_o ( clk_osc_usb_val )
);

///////////////////////////////////////
// Main Domain Clock Bypass
///////////////////////////////////////
ast_aon_main_pkg::clks_byp_main_to_aon_t clks_byp_main_to_aon;
logic clk_src_sys, clk_src_io, clk_src_usb;

`ifdef AST_BYPASS_CLK
logic clk_aon_ext;
assign clk_aon_ext = clk_osc_byp_i.aon;
`endif

ast_clks_byp_main u_ast_clks_byp_main (
  .vcmain_pok_i ( aon_to_main_i.pwr.vcmain_pok_h ),
  .vcmain_pok_por_i ( aon_to_main_i.pwr.vcmain_pok_por ),
  .deep_sleep_i ( aon_to_main_i.clk_osc.deep_sleep ),
  .scan_mode_i ( aon_to_main_i.scan_mode ),
  .scan_reset_ni ( aon_to_main_i.scan_reset_n ),
  .clk_ast_tlul_i ( aon_to_main_i.clk_rst.clk_ast_tlul ),
  .dft_clks_byp_i ( 1'b0 ),
  .dft_ext_is_96m_i ( 1'b1 ),
  .clk_src_io_pre_occ_i ( clk_osc_io ),
  .clk_src_sys_en_i ( clk_src_sys_en_i ),
  .clk_osc_sys_i ( clk_osc_sys ),
  .clk_osc_sys_val_i ( clk_osc_sys_val ),
  .clk_src_io_en_i ( clk_src_io_en_i ),
  .clk_osc_io_i ( clk_osc_io ),
  .clk_osc_io_val_i ( clk_osc_io_val ),
  .clk_src_usb_en_i ( clk_src_usb_en_i ),
  .clk_osc_usb_i ( clk_osc_usb ),
  .clk_osc_usb_val_i ( clk_osc_usb_val ),
  .clk_ast_ext_i ( clk_ast_ext_i ),
`ifdef AST_BYPASS_CLK
  .clk_ext_sys_i( clk_sys_ext ),
  .clk_ext_io_i( clk_io_ext ),
  .clk_ext_usb_i( clk_usb_ext ),
  .clk_ext_aon_i( clk_aon_ext ),
`endif
  .io_clk_byp_req_i ( io_clk_byp_req_i ),
  .all_clk_byp_req_i ( all_clk_byp_req_i ),
  .ext_freq_is_96m_i ( ext_freq_is_96m_i ),
  .aon_to_main_i ( clks_byp_aon_to_main ),
  .main_to_aon_o ( clks_byp_main_to_aon ),
  .io_clk_byp_ack_o ( io_clk_byp_ack_o ),
  .all_clk_byp_ack_o ( all_clk_byp_ack_o ),
  .force_scan_reset_o ( ),
  .clk_src_sys_o ( clk_src_sys ),
  .clk_src_sys_val_o ( clk_src_sys_val_o ),
  .clk_src_io_o ( clk_src_io ),
  .clk_src_io_val_o ( clk_src_io_val_o ),
  .clk_src_io_48m_o ( clk_src_io_48m_o ),
  .clk_src_usb_o ( clk_src_usb ),
  .clk_src_usb_val_o ( clk_src_usb_val_o )
);


// System source clock buffer
////////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_src_sys_buf (
  .clk_i ( clk_src_sys ),
  .clk_o ( clk_src_sys_o )
);

// IO source clock buffer
////////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_src_io_buf (
  .clk_i ( clk_src_io ),
  .clk_o ( clk_src_io_o )
);

// USB source clock buffer
////////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_src_usb_buf (
  .clk_i ( clk_src_usb ),
  .clk_o ( clk_src_usb_o )
);

///////////////////////////////////////
// Entropy (OS simplified - fewer ports)
///////////////////////////////////////
ast_entropy u_entropy (
  .entropy_rsp_i ( entropy_rsp_i ),
  .entropy_rate_i ( 4'd5 ),
  .clk_ast_es_i ( clk_ast_es_i ),
  .rst_ast_es_ni ( rst_ast_es_ni ),
  .clk_src_sys_i ( clk_src_sys_o ),
  .rst_src_sys_ni ( rst_src_sys_n ),
  .clk_src_sys_val_i ( clk_src_sys_val_o ),
  .clk_src_sys_jen_i ( prim_mubi_pkg::mubi4_test_true_loose(clk_src_sys_jen_i) ),
  .entropy_req_o ( entropy_req_o )
);

///////////////////////////////////////
// RNG (OS simplified - fewer ports)
///////////////////////////////////////
rng #(
  .EntropyStreams ( ast_pkg::EntropyStreams )
) u_rng (
  .clk_i ( aon_to_main_i.clk_rst.clk_ast_tlul ),
  .rst_ni ( aon_to_main_i.clk_rst.rst_ast_tlul_n ),
  .clk_ast_rng_i ( aon_to_main_i.clk_rst.clk_ast_rng ),
  .rst_ast_rng_ni ( aon_to_main_i.clk_rst.rst_ast_rng_n ),
  .rng_en_i ( rng_en_i ),
  .rng_fips_i ( rng_fips_i ),
  .scan_mode_i ( aon_to_main_i.scan_mode ),
  .rng_b_o ( rng_b_o ),
  .rng_val_o ( rng_val_o )
);

///////////////////////////////////////
// Output Assignments
///////////////////////////////////////
// Clock bypass interface to AON
assign main_to_aon_o.clks_byp = clks_byp_main_to_aon;

// Alert source from TLUL integrity error
assign main_to_aon_o.ot0_alert_src = '{p: intg_err, n: ~intg_err};
assign ot0_alert_src_o = main_to_aon_o.ot0_alert_src;

`ASSERT_KNOWN(ClkSrcIoKnownO_A, clk_src_io_o, 1, aon_to_main_i.pwr.vcmain_pok_h)
`ASSERT_KNOWN(ClkSrcIoValKnownO_A, clk_src_io_val_o, clk_src_io_o, rst_io_clk_n)
`ASSERT_KNOWN(ClkSrcIo48mKnownO_A, clk_src_io_48m_o, clk_src_io_o, rst_io_clk_n)
`ASSERT_KNOWN(ClkSrcSysKnownO_A, clk_src_sys_o, 1, aon_to_main_i.pwr.vcmain_pok_h)
`ASSERT_KNOWN(ClkSrcSysValKnownO_A, clk_src_sys_val_o, clk_src_sys_o, rst_sys_clk_n)
`ASSERT_KNOWN(ClkSrcUsbKnownO_A, clk_src_usb_o, 1, aon_to_main_i.pwr.vcmain_pok_h)
`ASSERT_KNOWN(ClkSrcUsbValKnownO_A, clk_src_usb_val_o, clk_src_usb_o, rst_usb_clk_n)
//
// Alert assertions for reg_we onehot check
`ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ERR(RegWeOnehot_A,
   u_reg, main_to_aon_o.ot0_alert_src.p, , , clk_ast_tlul_i, rst_ast_tlul_ni)
// RNG
`ASSERT_KNOWN(RngBKnownO_A, rng_b_o, aon_to_main_i.clk_rst.clk_ast_rng,
              aon_to_main_i.clk_rst.rst_ast_rng_n)
`ASSERT_KNOWN(RngValKnownO_A, rng_val_o, aon_to_main_i.clk_rst.clk_ast_rng,
              aon_to_main_i.clk_rst.rst_ast_rng_n)
// ES
`ASSERT_KNOWN(EntropyReeqKnownO_A, entropy_req_o, clk_ast_es_i,rst_ast_es_ni)
//
`ASSERT_KNOWN(LcClkBypAckEnKnownO_A, io_clk_byp_ack_o, clk_ast_tlul_i, rst_ast_tlul_ni)
`ASSERT_KNOWN(AllClkBypAckEnKnownO_A, all_clk_byp_ack_o, clk_ast_tlul_i, rst_ast_tlul_ni)
// TLUL
`ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid, clk_ast_tlul_i, rst_ast_tlul_ni)
`ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready, clk_ast_tlul_i, rst_ast_tlul_ni)
//
`ASSERT_KNOWN(InitDoneKnownO_A, ast_init_done_o, clk_ast_tlul_i, rst_ast_tlul_ni)

/////////////////////
// Unused Signals  //
/////////////////////
logic unused_sigs;

assign unused_sigs = ^{ reg2hw.rega0,
                        reg2hw.rega1,
                        reg2hw.rega2,
                        reg2hw.rega3,
                        reg2hw.rega4,
                        reg2hw.rega5,
                        reg2hw.rega6,
                        reg2hw.rega7,
                        reg2hw.rega8,
                        reg2hw.rega9,
                        reg2hw.rega10,
                        reg2hw.rega11,
                        reg2hw.rega12,
                        reg2hw.rega13,
                        reg2hw.rega14,
                        reg2hw.rega15,
                        reg2hw.rega16,
                        reg2hw.rega17,
                        reg2hw.rega18,
                        reg2hw.rega19,
                        reg2hw.rega20,
                        reg2hw.rega21,
                        reg2hw.rega22,
                        reg2hw.rega23,
                        reg2hw.rega24,
                        reg2hw.rega25,
                        reg2hw.rega26,
                        reg2hw.rega27,
                        reg2hw.rega28,
                        reg2hw.rega29,
                        reg2hw.rega30,
                        reg2hw.rega31,
                        reg2hw.rega32,
                        reg2hw.rega33,
                        reg2hw.rega34,
                        reg2hw.rega35,
                        reg2hw.rega36,
                        reg2hw.rega37,
                        reg2hw.regb   // [0:3]
                      };

endmodule : ast_main
