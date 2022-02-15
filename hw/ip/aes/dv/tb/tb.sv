// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import aes_env_pkg::*;
  import aes_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n, rst_shadowed_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire edn_req;
  keymgr_pkg::hw_key_req_t keymgr_key;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  rst_shadowed_if rst_shadowed_if(.rst_n(rst_n), .rst_shadowed_n(rst_shadowed_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);

  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  // edn_clk, edn_rst_n and edn_if is defined and driven in below macro
  `DV_EDN_IF_CONNECT
  `DV_ALERT_IF_CONNECT

  key_sideload_if sideload_if(.clk_i(clk), .rst_ni(rst_n));

  // dut
  aes #(
    // for now keep testing the unmasked implementation
    .SecMasking  ( 0                    ),
    .SecSBoxImpl ( aes_pkg::SBoxImplLut )
  ) dut (
    .clk_i            ( clk                               ),
    .rst_ni           ( rst_n                             ),
    .rst_shadowed_ni  ( rst_shadowed_n                    ),

    .idle_o           (                                   ),
    .lc_escalate_en_i ( lc_ctrl_pkg::Off                  ),
    .clk_edn_i        ( edn_clk                           ),
    .rst_edn_ni       ( edn_rst_n                         ),
    .edn_o            ( edn_if[0].req                     ),
    .edn_i            ( {edn_if[0].ack, edn_if[0].d_data} ),
    .keymgr_key_i     ( sideload_if.sideload_key          ),

    .tl_i             ( tl_if.h2d                         ),
    .tl_o             ( tl_if.d2h                         ),

    .alert_rx_i       ( alert_rx                          ),
    .alert_tx_o       ( alert_tx                          )
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif",
                                                 rst_shadowed_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual aes_cov_if)::set(null, "*.env", "aes_cov_if", dut.u_aes_cov_if );
    uvm_config_db#(virtual key_sideload_if)
                  ::set(null, "*.env.keymgr_sideload_agent*", "vif", sideload_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
