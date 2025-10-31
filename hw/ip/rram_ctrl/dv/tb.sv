// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // Dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import rram_ctrl_env_pkg::*;
  import rram_ctrl_test_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire                          clk;
  wire                          rst_n;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // Interfaces
  clk_rst_if                    clk_rst_if    (.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if       (interrupts);
  tl_if                         tl_core_if    (.clk(clk), .rst_n(rst_n));
  tl_if                         tl_host_if    ();
  tl_if                         tl_prim_if    ();
  misc_vif_t                    misc_if       ();

  `DV_ALERT_IF_CONNECT()

  // DUT
  rram_ctrl dut (
    .clk_i                (clk            ),
    .rst_ni               (rst_n          ),
    .tl_i                 (tl_core_if.h2d ),
    .tl_o                 (tl_core_if.d2h ),
    .alert_rx_i           (alert_rx       ),
    .alert_tx_o           (alert_tx       )
    // TODO: add remaining IOs and hook them
  );

  initial begin
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_*_core*", "vif", tl_core_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_*_host*", "vif", tl_host_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_*_prim*", "vif", tl_prim_if);
    uvm_config_db#(misc_vif_t)::set(null, "*.env", "misc_vif", misc_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule : tb
