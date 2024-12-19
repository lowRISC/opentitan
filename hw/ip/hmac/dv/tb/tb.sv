// Copyright lowRISC contributors (OpenTitan project).
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
  wire [NUM_MAX_INTERRUPTS-1:0]  interrupts;

  wire intr_hmac_done;
  wire intr_fifo_empty;
  wire intr_hmac_err;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));  // The rst_n is an input to the clk_rst_if
  reset_interface reset_if();
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(.pins(interrupts));
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  hmac_if hmac_if(.clk_i(clk), .rst_ni(rst_n));

  `DV_ALERT_IF_CONNECT()

  // dut
  hmac dut (
    .clk_i              ( clk            ),
    .rst_ni             ( rst_n          ),

    .tl_i               ( tl_if.h2d      ),
    .tl_o               ( tl_if.d2h      ),

    .alert_rx_i         ( alert_rx       ),
    .alert_tx_o         ( alert_tx       ),

    .intr_hmac_done_o   ( intr_hmac_done ),
    .intr_fifo_empty_o  ( intr_fifo_empty),
    .intr_hmac_err_o    ( intr_hmac_err  ),

    .idle_o             (hmac_if.idle)
  );

  assign interrupts[HmacDone]         = intr_hmac_done;
  assign interrupts[HmacMsgFifoEmpty] = intr_fifo_empty;
  assign interrupts[HmacErr]          = intr_hmac_err;

  // Reset agent
  assign reset_if.clk_i = clk;              // From the TB to the agent
  assign rst_n          = reset_if.rst_o;   // From the agent to the TB

  initial begin
    clk_rst_if.has_reset_agent = 1;
    clk_rst_if.set_active(.drive_rst_n_val(0));
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual reset_interface)::set(null, "*", "reset_vif", reset_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual hmac_if)::set(null, "*.env", "hmac_vif", hmac_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
