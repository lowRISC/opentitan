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

  wire                                    clk, rst_n, rst_shadowed_n;
  wire                                    devmode;
  wire [NUM_MAX_INTERRUPTS-1:0]           interrupts;
  wire                                    edn_req;
  wire [$bits(lc_ctrl_pkg::lc_tx_t) : 0]  lc_escalate;
  wire                                    idle;
  prim_mubi_pkg::mubi4_t                  idle_s;
  lc_ctrl_pkg::lc_tx_t                    lc_escalate_en;
  keymgr_pkg::hw_key_req_t                keymgr_key;


  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  rst_shadowed_if rst_shadowed_if(.rst_n(rst_n), .rst_shadowed_n(rst_shadowed_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);

  pins_if #(1) devmode_if(devmode);
  pins_if #($bits(lc_escalate)) lc_escalate_if (lc_escalate);
  pins_if #(1) idle_if (idle);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  // edn_clk, edn_rst_n and edn_if is defined and driven in below macro
  `DV_EDN_IF_CONNECT
  `DV_ALERT_IF_CONNECT()

  key_sideload_if sideload_if(.clk_i(clk), .rst_ni(rst_n), .sideload_key());
 //lc_ctrl_pkg::On
  assign lc_escalate_en = lc_escalate[0] ?
                          lc_ctrl_pkg::lc_tx_t'(lc_escalate[$bits(lc_ctrl_pkg::lc_tx_t):1]) :
                          lc_ctrl_pkg::Off;

  assign idle = (idle_s == prim_mubi_pkg::MuBi4True) ? 1 : 0;

  // dut
  aes #(
    .SecMasking  ( `EN_MASKING   ),
    .SecSBoxImpl ( `SBOX_IMPL    )
  ) dut (
    .clk_i            ( clk                               ),
    .rst_ni           ( rst_n                             ),
    .rst_shadowed_ni  ( rst_shadowed_n                    ),

    .idle_o           ( idle_s                            ),
    .lc_escalate_en_i ( lc_escalate_en                    ),
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

    lc_escalate_if.drive('0);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif",
                                                 rst_shadowed_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual aes_cov_if)::set(null, "*.env", "aes_cov_if", dut.u_aes_cov_if );
    uvm_config_db#(virtual key_sideload_if)
                   ::set(null, "*.env.keymgr_sideload_agent*", "vif", sideload_if);

    uvm_config_db#(virtual pins_if #($bits(lc_ctrl_pkg::lc_tx_t) + 1))
                   ::set(null, "*.env", "lc_escalate_vif", lc_escalate_if);
    uvm_config_db#(virtual pins_if #(1))
                   ::set(null, "*.env", "idle_vif", idle_if);
    uvm_config_db#(virtual aes_reseed_if)::set(null, "*.env", "aes_reseed_vif",
                                               dut.u_aes_reseed_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  if (`EN_MASKING) begin : gen_aes_masking_reseed_vif
    initial begin
      uvm_config_db#(virtual aes_masking_reseed_if)
                     ::set(null, "*.env", "aes_masking_reseed_vif", dut.u_aes_masking_reseed_if);
    end
  end
endmodule
