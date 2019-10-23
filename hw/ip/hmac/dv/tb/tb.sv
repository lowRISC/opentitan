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
  wire [NUM_MAX_ALERTS-1:0] alerts;

  wire intr_hmac_done;
  wire intr_fifo_full;
  wire intr_hmac_err;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(.pins(interrupts));
  pins_if #(NUM_MAX_ALERTS) alerts_if(.pins(alerts));
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  pins_if #(1) d2h_a_ready_if(tl_if.d2h.a_ready);

  // dut
  hmac dut (
    .clk_i          (clk       ),
    .rst_ni         (rst_n     ),

    .tl_i           (tl_if.h2d ),
    .tl_o           (tl_if.d2h ),

    .intr_hmac_done_o   (intr_hmac_done),
    .intr_fifo_full_o   (intr_fifo_full),
    .intr_hmac_err_o    (intr_hmac_err)
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
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(tlul_assert_ctrl_vif)::set(null, "*.env", "tlul_assert_ctrl_vif",
        dut.tlul_assert_device.tlul_assert_ctrl_if);
    uvm_config_db#(d2h_a_ready_vif)::set(null, "*.env", "d2h_a_ready_vif", d2h_a_ready_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
