// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tb;
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import keymgr_dpe_env_pkg::*;
  import keymgr_dpe_test_pkg::*;
  import keymgr_dpe_reg_pkg::NumAlerts;
  import cip_base_pkg::EDN_DATA_WIDTH;
  import keymgr_dpe_pkg::KdfEngineBoth;

  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk;
  wire rst_n;
  wire rst_shadowed_n;
  wire edn_clk;
  wire edn_rst_n;

  // KMAC app's req / rsp interface. The request carries the message utilized in the key derivation
  // function by KMAC. The response carries the derived child key.
  wire kmac_pkg::app_req_t kmac_req;
  wire kmac_pkg::app_rsp_t kmac_rsp;

  // OTBN app's req / rsp interface. The request carries the message utilized in the HMAC-based key
  // derivation function by OTBN firmware. The response carries the derived child key.
  wire kmac_pkg::app_req_t otbn_req;
  wire kmac_pkg::app_rsp_t otbn_rsp;

  // Operation done interrupt from keymgr_dpe
  wire                          intr_op_done;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  assign interrupts = NUM_MAX_INTERRUPTS'(intr_op_done);

  // Alert interface to keymgr_dpe
  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx;
  prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx;

  clk_rst_if      clk_rst_if (.clk(clk), .rst_n(rst_n));
  rst_shadowed_if rst_shadowed_if (.rst_n(rst_n), .rst_shadowed_n(rst_shadowed_n));
  keymgr_dpe_if   keymgr_dpe_if(.clk(clk), .rst_n(rst_n));
  kmac_app_if     kmac_if (.clk_i(clk), .rst_ni(rst_n), .req(kmac_req), .rsp(kmac_rsp));

  // For now, instantiate KMAC interface as OTBN until we get a new HKDF agent. Tracked in #32188.
  kmac_app_if     otbn_if (.clk_i(clk), .rst_ni(rst_n), .req(otbn_req), .rsp(otbn_rsp));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if (interrupts);
  alert_if        alert_if[NumAlerts] (.clk(clk), .rst_n(rst_n));
  tl_if           tl_if (.clk(clk), .rst_n(rst_n));

  clk_rst_if      edn_clk_rst_if (.clk(edn_clk), .rst_n(edn_rst_n));
  push_pull_if #(.DeviceDataWidth(EDN_DATA_WIDTH)) edn_if (.clk(edn_clk), .rst_n(edn_rst_n));

  keymgr_dpe #(
    .NumInstHwSlot      (DvNumInstHwSlot),
    .NumBootStages      (DvBootStages),
    .NumRomDigestInputs (DvNumRomDigestInputs),
    .KdfEngineSel       (KdfEngineBoth)
  ) dut (
    .clk_i                (clk),
    .rst_ni               (rst_n),
    .rst_shadowed_ni      (rst_shadowed_n),
    .clk_edn_i            (edn_if.clk),
    .rst_edn_ni           (edn_if.rst_n),
    .aes_key_o            (keymgr_dpe_if.aes_key),
    .otbn_key_o           (keymgr_dpe_if.otbn_key),
    .hmac_key_o           (keymgr_dpe_if.hmac_key),
    .kmac_key_o           (keymgr_dpe_if.kmac_key),
    .kmac_app_o           (kmac_req),
    .kmac_app_i           (kmac_rsp),
    .otbn_app_o           (otbn_req),
    .otbn_app_i           (otbn_rsp),
    .sensitive_key_o      (), // Connect to HKDF agent once it exists.
    .kmac_en_masking_i    (1'b1),
    .lc_keymgr_en_i       (keymgr_dpe_if.keymgr_dpe_en),
    .lc_keymgr_div_i      (keymgr_dpe_if.keymgr_dpe_div),
    .creator_root_key_i   (keymgr_dpe_if.creator_root_key),
    .secondary_root_key_i (keymgr_dpe_if.secondary_root_key),
    .creator_seed_i       (keymgr_dpe_if.creator_seed),
    .owner_seed_i         (keymgr_dpe_if.owner_seed),
    .device_id_i          (keymgr_dpe_if.otp_device_id),
    .field_entropy_i      (keymgr_dpe_if.field_entropy),
    .rom_digest_i         (keymgr_dpe_if.rom_digests),
    .edn_o                (edn_if.req),
    .edn_i                ({edn_if.ack, edn_if.d_data}),
    .intr_op_done_o       (intr_op_done),
    .alert_rx_i           (alert_rx),
    .alert_tx_o           (alert_tx),
    .tl_i                 (tl_if.h2d),
    .tl_o                 (tl_if.d2h)
  );

  bind dut.u_ctrl keymgr_dpe_ctrl_if u_if (.clk_i, .rst_ni);

  // Connect keymgr_dpe and KMAC interface.
  assign keymgr_dpe_if.kmac_data_req = kmac_req;
  assign keymgr_dpe_if.kmac_data_rsp = kmac_rsp;

  // No agent drives otbn_if yet, so otbn_rsp would float. Tie it to its default value until the
  // HKDF agent exists (#32188).
  assign otbn_rsp = kmac_pkg::APP_RSP_DEFAULT;

  // Connect keymgr_dpe and EDN interface.
  assign keymgr_dpe_if.edn_clk   = edn_if.clk;
  assign keymgr_dpe_if.edn_rst_n = edn_if.rst_n;
  assign keymgr_dpe_if.edn_req   = edn_if.req;
  assign keymgr_dpe_if.edn_ack   = edn_if.ack;
  assign keymgr_dpe_if.lfsr_en   = dut.lfsr_en;

  // Connect alert pins to alert interface and register VIFs in config_db
  for (genvar i = 0; i < NumAlerts; i++) begin : gen_connect_alert_if
    assign alert_if[i].alert_tx = alert_tx[i];
    assign alert_rx[i] = alert_if[i].alert_rx;
    initial begin
      automatic string agent_path = $sformatf("*.env.m_alert_agent_%0s", LIST_OF_ALERTS[i]);
      uvm_config_db#(virtual alert_if)::set(null, agent_path, "vif", alert_if[i]);
    end
  end

  assign keymgr_dpe_if.internal_key_slots = dut.u_ctrl.key_slots_q;

  initial begin
    // Drive clk and rst_n from clk_rst_if.
    clk_rst_if.set_active();
    edn_clk_rst_if.set_active();

    // Set all the interface handles in config_db for their respective agents.
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "edn_clk_rst_vif", edn_clk_rst_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null,
                                                 "*.env",
                                                 "rst_shadowed_vif",
                                                 rst_shadowed_if);
    uvm_config_db#(virtual keymgr_dpe_ctrl_if)::set(null,
                                                    "*.env",
                                                    "keymgr_dpe_ctrl_vif",
                                                    dut.u_ctrl.u_if);
    uvm_config_db#(virtual keymgr_dpe_if)::set(null, "*.env", "keymgr_dpe_vif", keymgr_dpe_if);
    uvm_config_db#(virtual kmac_app_if)::set(null, "*env.m_kmac_agent", "vif", kmac_if);
    uvm_config_db#(virtual kmac_app_if)::set(null, "*env.m_otbn_agent", "vif", otbn_if);
    uvm_config_db#(virtual push_pull_if#(.DeviceDataWidth(EDN_DATA_WIDTH)))
                 ::set(null, "*.env.m_edn_pull_agent*", "vif", edn_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);

    run_test();
  end
endmodule
