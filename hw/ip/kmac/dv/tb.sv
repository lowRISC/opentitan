// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import kmac_env_pkg::*;
  import kmac_test_pkg::*;
  import kmac_reg_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n, rst_shadowed_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  // keymgr/kmac sideload wires
  keymgr_pkg::hw_key_req_t kmac_sideload_key;
  // kmac_app interfaces
  kmac_pkg::app_req_t [kmac_pkg::NumAppIntf-1:0] app_req;
  kmac_pkg::app_rsp_t [kmac_pkg::NumAppIntf-1:0] app_rsp;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  rst_shadowed_if rst_shadowed_if(.rst_n(rst_n), .rst_shadowed_n(rst_shadowed_n));
  kmac_if kmac_if(.clk_i(clk), .rst_ni(rst_n));

  pins_if #(1)                   devmode_if(devmode);
  pins_if #(NUM_MAX_INTERRUPTS)  intr_if(interrupts);

  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  key_sideload_if sideload_if(
    .clk_i        (clk),
    .rst_ni       (rst_n),
    .sideload_key (kmac_sideload_key)
  );

  kmac_app_intf kmac_app_if[kmac_pkg::NumAppIntf](.clk(clk), .rst_n(rst_n));

  // edn_clk, edn_rst_n and edn_if is defined and driven in below macro
  `DV_EDN_IF_CONNECT

  `DV_ALERT_IF_CONNECT

  // dut

  kmac #(.EnMasking(`EN_MASKING), .ReuseShare(`REUSE_SHARE)) dut (
    .clk_i              (clk            ),
    .rst_ni             (rst_n          ),
    .rst_shadowed_ni    (rst_shadowed_n ),

    // TLUL interface
    .tl_i               (tl_if.h2d ),
    .tl_o               (tl_if.d2h ),

    // Alerts
    .alert_rx_i         (alert_rx ),
    .alert_tx_o         (alert_tx ),

    // life cycle escalation input
    .lc_escalate_en_i   (kmac_if.lc_escalate_en_i ),

    // KeyMgr sideload key interface
    .keymgr_key_i       (kmac_sideload_key),

    // KeyMgr KDF datapath
    //
    // TODO: this is set to 0 for the time being to get the csr tests passing.
    //       this will eventually be hooked up to the kmac<->keymgr agent.
    .app_i       (app_req ),
    .app_o       (app_rsp ),

    // Interrupts
    .intr_kmac_done_o   (interrupts[KmacDone]      ),
    .intr_fifo_empty_o  (interrupts[KmacFifoEmpty] ),
    .intr_kmac_err_o    (interrupts[KmacErr]       ),

    // Idle interface
    .idle_o             (kmac_if.idle_o ),

    // TODO: check this output signal.
    .en_masking_o       (kmac_if.en_masking_o ),

    // EDN interface
    .clk_edn_i          (edn_clk                           ),
    .rst_edn_ni         (edn_rst_n                         ),
    .entropy_o          (edn_if[0].req                     ),
    .entropy_i          ({edn_if[0].ack, edn_if[0].d_data} )
  );

  for (genvar i = 0; i < kmac_pkg::NumAppIntf; i++) begin : gen_kmac_app_intf
    assign app_req[i]                   = kmac_app_if[i].kmac_data_req;
    assign kmac_app_if[i].kmac_data_rsp = app_rsp[i];
    assign kmac_if.app_err_o[i] = app_rsp[i].error;

    initial begin
      uvm_config_db#(virtual kmac_app_intf)::set(null,
          $sformatf("*env.m_kmac_app_agent[%0d]*", i), "vif", kmac_app_if[i]);
    end
  end

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif",
                                                 rst_shadowed_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual key_sideload_if)::set(null, "*.env.keymgr_sideload_agent*",
                                                 "vif", sideload_if);
    uvm_config_db#(virtual kmac_if)::set(null, "*.env", "kmac_vif", kmac_if);

    // Random drive lc_escalation signals.
    $assertoff(0, tb.dut.u_prim_lc_sync.PrimLcSyncCheckTransients_A);
    $assertoff(0, tb.dut.u_prim_lc_sync.PrimLcSyncCheckTransients0_A);
    $assertoff(0, tb.dut.u_prim_lc_sync.PrimLcSyncCheckTransients1_A);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  // This assertion only exists when en_masking parameter is set.
  // This assertion will not be true if Kmac is interrupted by lc_escalate_en signal.
  if (`EN_MASKING) begin : gen_assert_disable_for_masking_mode
    initial begin
      bit disable_lc_asserts;
      void'($value$plusargs("disable_lc_asserts=%0b", disable_lc_asserts));
      if (disable_lc_asserts) begin
        $assertoff(0, tb.dut.u_sha3.u_keccak.u_keccak_p.gen_selperiod_chk.SelStayTwoCycleIf1_A);
      end
    end
  end

endmodule
