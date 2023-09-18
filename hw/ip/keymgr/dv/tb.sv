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

  wire clk, rst_n, rst_shadowed_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  rst_shadowed_if rst_shadowed_if(.rst_n(rst_n), .rst_shadowed_n(rst_shadowed_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  keymgr_if keymgr_if(.clk(clk), .rst_n(rst_n));
  kmac_app_intf keymgr_kmac_intf(.clk(clk), .rst_n(rst_n));

  // connect KDF interface for assertion check
  assign keymgr_if.kmac_data_req = keymgr_kmac_intf.kmac_data_req;
  assign keymgr_if.kmac_data_rsp = keymgr_kmac_intf.kmac_data_rsp;

  `DV_ALERT_IF_CONNECT()

  // edn_clk, edn_rst_n and edn_if are defined and driven in below macro
  `DV_EDN_IF_CONNECT

  assign keymgr_if.edn_clk   = edn_if[0].clk;
  assign keymgr_if.edn_rst_n = edn_if[0].rst_n;
  assign keymgr_if.edn_req   = edn_if[0].req;
  assign keymgr_if.edn_ack   = edn_if[0].ack;

  // dut
  keymgr #(
    // TODO(opentitan-integrated/issues/332):
    // need to model the OTP seed input
    .UseOtpSeedsInsteadOfFlash(0)
  ) dut (
    .clk_i                (clk           ),
    .rst_ni               (rst_n         ),
    .rst_shadowed_ni      (rst_shadowed_n),
    .clk_edn_i            (edn_clk       ),
    .rst_edn_ni           (edn_rst_n     ),
    .aes_key_o            (keymgr_if.aes_key),
    .otbn_key_o           (keymgr_if.otbn_key),
    .kmac_key_o           (keymgr_if.kmac_key),
    .kmac_data_o          (keymgr_kmac_intf.kmac_data_req),
    .kmac_data_i          (keymgr_kmac_intf.kmac_data_rsp),
    .kmac_en_masking_i    (1'b1),
    .lc_keymgr_en_i       (keymgr_if.keymgr_en),
    .lc_keymgr_div_i      (keymgr_if.keymgr_div),
    .otp_key_i            (keymgr_if.otp_key),
    .otp_device_id_i      (keymgr_if.otp_device_id),
    .rom_digest_i         (keymgr_if.rom_digests),
    .edn_o                (edn_if[0].req),
    .edn_i                ({edn_if[0].ack, edn_if[0].d_data}),
    .flash_i              (keymgr_if.flash),
    .intr_op_done_o       (interrupts[0]),
    .alert_rx_i           (alert_rx   ),
    .alert_tx_o           (alert_tx   ),
    .tl_i                 (tl_if.h2d  ),
    .tl_o                 (tl_if.d2h  )
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
    uvm_config_db#(virtual keymgr_if)::set(null, "*.env", "keymgr_vif", keymgr_if);
    uvm_config_db#(virtual kmac_app_intf)::set(null,
                   "*env.m_keymgr_kmac_agent*", "vif", keymgr_kmac_intf);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end
endmodule
