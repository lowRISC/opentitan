// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import alert_handler_env_pkg::*;
  import alert_handler_test_pkg::*;
  import alert_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n, rst_shadowed_n;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire [NUM_MAX_ESC_SEV-1:0]    esc_en;
  wire [NUM_CRASHDUMP-1:0]      crashdump;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  rst_shadowed_if rst_shadowed_if(.rst_n(rst_n), .rst_shadowed_n(rst_shadowed_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(NUM_CRASHDUMP) crashdump_if(crashdump);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  alert_handler_if alert_handler_if(.clk(clk), .rst_n(rst_n));
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
    assign alert_handler_if.alert_ping_reqs[k] = dut.gen_alerts[k].u_alert_receiver.ping_req_i;
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
    assign probe_if[k].esc_en = dut.esc_sig_req[k];
    assign alert_handler_if.esc_ping_reqs[k] = dut.gen_esc_sev[k].u_esc_sender.ping_req_i;
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
    .rst_shadowed_ni      ( rst_shadowed_n),
    .clk_edn_i            ( edn_clk       ),
    .rst_edn_ni           ( edn_rst_n     ),
    .tl_i                 ( tl_if.h2d     ),
    .tl_o                 ( tl_if.d2h     ),
    .intr_classa_o        ( interrupts[0] ),
    .intr_classb_o        ( interrupts[1] ),
    .intr_classc_o        ( interrupts[2] ),
    .intr_classd_o        ( interrupts[3] ),
    .lpg_cg_en_i          ( alert_handler_if.lpg_cg_en  ),
    .lpg_rst_en_i         ( alert_handler_if.lpg_rst_en ),
    .crashdump_o          ( crashdump     ),
    .edn_o                ( edn_if[0].req    ),
    .edn_i                ( {edn_if[0].ack, edn_if[0].d_data} ),
    .alert_rx_o           ( alert_rx      ),
    .alert_tx_i           ( alert_tx      ),
    .esc_rx_i             ( esc_rx        ),
    .esc_tx_o             ( esc_tx        )
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif",
                                                 rst_shadowed_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(crashdump_vif)::set(null, "*.env", "crashdump_vif", crashdump_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual alert_handler_if)::set(null, "*.env", "alert_handler_vif",
                   alert_handler_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
