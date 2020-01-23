// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import alert_handler_env_pkg::*;
  import alert_handler_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire [NUM_MAX_ESC_SEV-1:0]    esc_en;
  wire entropy;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(NUM_MAX_ESC_SEV) esc_en_if(esc_en);
  pins_if #(1) entropy_if(entropy);
  pins_if #(1) devmode_if();
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  // dut signals
  prim_pkg::alert_rx_t [alert_pkg::NAlerts-1:0] alert_rx;
  prim_pkg::alert_tx_t [alert_pkg::NAlerts-1:0] alert_tx;

  prim_pkg::esc_rx_t [alert_pkg::N_ESC_SEV-1:0] esc_rx;
  prim_pkg::esc_tx_t [alert_pkg::N_ESC_SEV-1:0] esc_tx;

  alert_if alert_host_if[alert_pkg::NAlerts](.clk(clk), .rst_n(rst_n));
  for (genvar k = 0; k < alert_pkg::NAlerts; k++) begin : gen_alert_if
    assign alert_tx[k].alert_p = alert_host_if[k].alert_tx.alert_p;
    assign alert_tx[k].alert_n = alert_host_if[k].alert_tx.alert_n;
    assign alert_host_if[k].alert_rx.ack_p  = alert_rx[k].ack_p;
    assign alert_host_if[k].alert_rx.ack_n  = alert_rx[k].ack_n;
    assign alert_host_if[k].alert_rx.ping_p = alert_rx[k].ping_p;
    assign alert_host_if[k].alert_rx.ping_n = alert_rx[k].ping_n;
    initial begin
      uvm_config_db#(virtual alert_if)::set(null, $sformatf("*.env.alert_host_agent[%0d]", k),
                                            "vif", alert_host_if[k]);
    end
  end

  alert_if esc_device_if[alert_pkg::N_ESC_SEV](.clk(clk), .rst_n(rst_n));
  for (genvar k = 0; k < alert_pkg::N_ESC_SEV; k++) begin : gen_esc_if
    assign esc_rx[k].resp_p = esc_device_if[k].esc_rx.resp_p;
    assign esc_rx[k].resp_n = esc_device_if[k].esc_rx.resp_n;
    assign esc_device_if[k].esc_tx.esc_p = esc_tx[k].esc_p;
    assign esc_device_if[k].esc_tx.esc_n = esc_tx[k].esc_n;
    initial begin
      uvm_config_db#(virtual alert_if)::set(null, $sformatf("*.env.esc_device_agent[%0d]", k),
                                            "vif", esc_device_if[k]);
    end
  end
  // main dut
  alert_handler dut (
    .clk_i                ( clk           ),
    .rst_ni               ( rst_n         ),
    .tl_i                 ( tl_if.h2d     ),
    .tl_o                 ( tl_if.d2h     ),
    .intr_classa_o        ( interrupts[0] ),
    .intr_classb_o        ( interrupts[1] ),
    .intr_classc_o        ( interrupts[2] ),
    .intr_classd_o        ( interrupts[3] ),
    .crashdump_o          (               ),
    .entropy_i            ( entropy       ),
    .alert_rx_o           ( alert_rx      ),
    .alert_tx_i           ( alert_tx      ),
    .esc_rx_i             ( esc_rx        ),
    .esc_tx_o             ( esc_tx        )
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(esc_en_vif)::set(null, "*.env", "esc_en_vif", esc_en_if);
    uvm_config_db#(entropy_vif)::set(null, "*.env", "entropy_vif", entropy_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(tlul_assert_ctrl_vif)::set(null, "*.env", "tlul_assert_ctrl_vif",
        dut.tlul_assert_device.tlul_assert_ctrl_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
