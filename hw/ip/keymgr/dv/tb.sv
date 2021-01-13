// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import keymgr_env_pkg::*;
  import keymgr_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  keymgr_if keymgr_if(.clk(clk), .rst_n(rst_n));
  keymgr_kmac_intf keymgr_kmac_intf(.clk(clk), .rst_n(rst_n));

  // connect KDF interface for assertion check
  assign keymgr_if.kmac_data_req = keymgr_kmac_intf.kmac_data_req;
  assign keymgr_if.kmac_data_rsp = keymgr_kmac_intf.kmac_data_rsp;

  `DV_ALERT_IF_CONNECT

  // edn_clk, edn_rst_n and edn_if are defined and driven in below macro
  `DV_EDN_IF_CONNECT

  // dut
  keymgr dut (
    .clk_i                (clk        ),
    .rst_ni               (rst_n      ),
    .clk_edn_i            (edn_clk    ),
    .rst_edn_ni           (edn_rst_n  ),
    .aes_key_o            (keymgr_if.aes_key),
    .hmac_key_o           (keymgr_if.hmac_key),
    .kmac_key_o           (keymgr_if.kmac_key),
    .kmac_data_o          (keymgr_kmac_intf.kmac_data_req),
    .kmac_data_i          (keymgr_kmac_intf.kmac_data_rsp),
    .lc_keymgr_en_i       (keymgr_if.keymgr_en),
    .lc_keymgr_div_i      (keymgr_if.keymgr_div),
    .otp_key_i            (keymgr_if.otp_key),
    .otp_hw_cfg_i         (keymgr_if.otp_hw_cfg),
    .edn_o                (edn_if.req),
    .edn_i                ({edn_if.ack, edn_if.d_data}),
    .flash_i              (keymgr_if.flash),
    .intr_op_done_o       (interrupts),
    .alert_rx_i           (alert_rx   ),
    .alert_tx_o           (alert_tx   ),
    .tl_i                 (tl_if.h2d  ),
    .tl_o                 (tl_if.d2h  )
  );

  initial begin
    // these SVA checks the keymgr_en is either Off or On, we will use more than these 2 values.
    // If it's not On, it should be off
    $assertoff(0, tb.dut.u_lc_keymgr_en_sync.CheckTransients_A);
    $assertoff(0, tb.dut.u_lc_keymgr_en_sync.CheckTransients0_A);
    $assertoff(0, tb.dut.u_lc_keymgr_en_sync.CheckTransients1_A);

    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual keymgr_if)::set(null, "*.env", "keymgr_vif", keymgr_if);
    uvm_config_db#(virtual keymgr_kmac_intf)::set(null,
                   "*env.m_keymgr_kmac_agent*", "vif", keymgr_kmac_intf);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
