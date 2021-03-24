// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire [NUM_MAX_ESC_SEV-1:0]    esc_en;
  wire entropy;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) entropy_if(entropy);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  alert_esc_if esc_device_if [NUM_ESCS](.clk(clk), .rst_n(rst_n));
  alert_esc_if alert_host_if [NUM_ALERTS](.clk(clk), .rst_n(rst_n));
  alert_esc_probe_if probe_if[NUM_ESCS](.clk(clk), .rst_n(rst_n));

  // dut signals
  prim_alert_pkg::alert_rx_t [NUM_ALERTS-1:0] alert_rx;
  prim_alert_pkg::alert_tx_t [NUM_ALERTS-1:0] alert_tx;

  prim_esc_pkg::esc_rx_t [NUM_ESCS-1:0] esc_rx;
  prim_esc_pkg::esc_tx_t [NUM_ESCS-1:0] esc_tx;

  for (genvar k = 0; k < NUM_ALERTS; k++) begin : gen_alert_if
    assign alert_tx[k].alert_p = alert_host_if[k].alert_tx.alert_p;
    assign alert_tx[k].alert_n = alert_host_if[k].alert_tx.alert_n;
    assign alert_host_if[k].alert_rx.ack_p  = alert_rx[k].ack_p;
    assign alert_host_if[k].alert_rx.ack_n  = alert_rx[k].ack_n;
    assign alert_host_if[k].alert_rx.ping_p = alert_rx[k].ping_p;
    assign alert_host_if[k].alert_rx.ping_n = alert_rx[k].ping_n;
    initial begin
      uvm_config_db#(virtual alert_esc_if)::set(null, $sformatf("*.env.alert_host_agent[%0d]", k),
                                                "vif", alert_host_if[k]);
    end
  end

  for (genvar k = 0; k < NUM_ESCS; k++) begin : gen_esc_if
    assign esc_rx[k].resp_p = esc_device_if[k].esc_rx.resp_p;
    assign esc_rx[k].resp_n = esc_device_if[k].esc_rx.resp_n;
    assign esc_device_if[k].esc_tx.esc_p = esc_tx[k].esc_p;
    assign esc_device_if[k].esc_tx.esc_n = esc_tx[k].esc_n;
    // TODO: add assertions to check the probed signal
    assign probe_if[k].esc_en = dut.esc_sig_req[k];
    initial begin
      uvm_config_db#(virtual alert_esc_if)::set(null, $sformatf("*.env.esc_device_agent[%0d]", k),
                                                "vif", esc_device_if[k]);
      uvm_config_db#(virtual alert_esc_probe_if)::set(null,
          $sformatf("*.env.esc_device_agent[%0d]", k), "probe_vif", probe_if[k]);
    end
  end

  // edn_clk, edn_rst_n and edn_if are defined and driven in below macro
  `DV_EDN_IF_CONNECT

  // main dut
  alert_handler dut (
    .clk_i                ( clk           ),
    .rst_ni               ( rst_n         ),
    .clk_edn_i            ( edn_clk       ),
    .rst_edn_ni           ( edn_rst_n     ),
    .tl_i                 ( tl_if.h2d     ),
    .tl_o                 ( tl_if.d2h     ),
    .intr_classa_o        ( interrupts[0] ),
    .intr_classb_o        ( interrupts[1] ),
    .intr_classc_o        ( interrupts[2] ),
    .intr_classd_o        ( interrupts[3] ),
    .crashdump_o          (               ),
    .edn_o                ( edn_if.req    ),
    .edn_i                ( {edn_if.ack, edn_if.d_data} ),
    .alert_rx_o           ( alert_rx      ),
    .alert_tx_i           ( alert_tx      ),
    .esc_rx_i             ( esc_rx        ),
    .esc_tx_o             ( esc_tx        )
  );

  initial begin
    static bit reduce_ping_timer_wait_cycles = 0;
    void'($value$plusargs("reduce_ping_timer_wait_cycles=%0b", reduce_ping_timer_wait_cycles));
    if (reduce_ping_timer_wait_cycles) force dut.i_ping_timer.wait_cyc_mask_i = 24'h3FFFF;
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(entropy_vif)::set(null, "*.env", "entropy_vif", entropy_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
