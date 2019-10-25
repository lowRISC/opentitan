// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import hmac_env_pkg::*;
  import hmac_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire [NUM_MAX_ALERTS-1:0]     alerts;
  wire [NUM_MAX_ALERTS-1:0]     ping_ok;
  wire [NUM_MAX_ALERTS-1:0]     ping_en;
  wire [NUM_MAX_ALERTS-1:0]     integ_fail;
  prim_pkg::alert_rx_t [hmac_pkg::NumAlerts-1:0] alert_rx;
  prim_pkg::alert_tx_t [hmac_pkg::NumAlerts-1:0] alert_tx;

  wire intr_hmac_done;
  wire intr_fifo_full;
  wire intr_hmac_err;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(.pins(interrupts));
  pins_if #(NUM_MAX_ALERTS) alerts_if(.pins(alerts));
  pins_if #(NUM_MAX_ALERTS) ping_ok_if(.pins(ping_ok));
  pins_if #(NUM_MAX_ALERTS) ping_en_if(.pins(ping_en));
  pins_if #(NUM_MAX_ALERTS) integ_fail_if(.pins(integ_fail));
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));


  // alert receivers
  logic [hmac_pkg::NumAlerts-1:0] ping_p, ping_n, ack_p, ack_n, alert_p, alert_n;
  for (genvar j = 0; j < hmac_pkg::NumAlerts; j++) begin : gen_alert_rx
    prim_alert_receiver #(
      .AsyncOn(hmac_pkg::AlertAsyncOn[j])
    ) i_prim_alert_receiver (
      .clk_i        ( clk           ),
      .rst_ni       ( rst_n         ),
      .ping_en_i    ( ping_en[j]    ),
      .ping_ok_o    ( ping_ok[j]    ),
      .integ_fail_o ( integ_fail[j] ),
      .alert_o      ( alert[j]      ),
      .alert_rx_o   ( alert_rx[j]   ),
      .alert_tx_i   ( alert_tx[j]   )
    );
  end : gen_alert_rx


  // dut
  hmac dut (
    .clk_i              ( clk            ),
    .rst_ni             ( rst_n          ),

    .tl_i               ( tl_if.h2d      ),
    .tl_o               ( tl_if.d2h      ),

    .intr_hmac_done_o   ( intr_hmac_done ),
    .intr_fifo_full_o   ( intr_fifo_full ),
    .intr_hmac_err_o    ( intr_hmac_err  ),

    .alert_rx_i         ( alert_rx       ),
    .alert_tx_o         ( alert_tx       )
  );

  assign interrupts[HmacDone]        = intr_hmac_done;
  assign interrupts[HmacMsgFifoFull] = intr_fifo_full;
  assign interrupts[HmacErr]         = intr_hmac_err;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(alerts_vif)::set(null, "*.env", "alerts_vif", alerts_if);
    uvm_config_db#(ping_ok_vif)::set(null, "*.env", "ping_ok_vif", ping_ok_if);
    uvm_config_db#(ping_en_vif)::set(null, "*.env", "ping_en_vif", ping_en_if);
    uvm_config_db#(integ_fail_vif)::set(null, "*.env", "integ_fail_vif", integ_fail_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(tlul_assert_vif)::set(null, "*.env", "tlul_assert_vif",
                                         tb.dut.tlul_assert_host);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
