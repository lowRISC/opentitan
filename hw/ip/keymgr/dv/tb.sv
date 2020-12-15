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
  push_pull_if #(.DeviceDataWidth(cip_base_pkg::EDN_DATA_WIDTH)) edn_if(.clk(clk), .rst_n(rst_n));

  `DV_ALERT_IF_CONNECT

  // dut
  keymgr dut (
    .clk_i                (clk        ),
    .rst_ni               (rst_n      ),
    .clk_edn_i            (clk        ),
    .rst_edn_ni           (rst_n      ),
    .aes_key_o            (keymgr_if.aes_key),
    .hmac_key_o           (keymgr_if.hmac_key),
    .kmac_key_o           (keymgr_if.kmac_key),
    .kmac_data_o          (keymgr_kmac_intf.kmac_data_req),
    .kmac_data_i          (keymgr_kmac_intf.kmac_data_rsp),
    .lc_keymgr_en_i       (lc_ctrl_pkg::On),
    .lc_keymgr_div_i      (keymgr_if.keymgr_div),
    .otp_key_i            (keymgr_if.otp_key),
    .otp_i                (keymgr_if.otp),
    .edn_o                (edn_if.req),
    .edn_i                ({edn_if.ack, edn_if.d_data}),
    .flash_i              (keymgr_if.flash),
    .intr_op_done_o       (interrupts),
    .alert_rx_i           (alert_rx   ),
    .alert_tx_o           (alert_tx   ),
    .tl_i                 (tl_if.h2d  ),
    .tl_o                 (tl_if.d2h  )
    // TODO: add remaining IOs and hook them
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual keymgr_if)::set(null, "*.env", "keymgr_vif", keymgr_if);
    uvm_config_db#(virtual keymgr_kmac_intf)::set(null,
                   "*env.m_keymgr_kmac_agent*", "vif", keymgr_kmac_intf);
    uvm_config_db#(virtual push_pull_if#(.DeviceDataWidth(cip_base_pkg::EDN_DATA_WIDTH)))::set
                   (null, "*env.m_edn_pull_agent*", "vif", edn_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
