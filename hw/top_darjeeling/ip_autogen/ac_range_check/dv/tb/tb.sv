// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // Dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import ac_range_check_env_pkg::*;
  import ac_range_check_test_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire                          clk;
  wire                          rst_n;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire                          rst_shadowed_n;
  wire                          intr_deny_cnt_reached;

  // Interfaces
  pins_if #(NUM_MAX_INTERRUPTS) intr_if (interrupts);
  clk_rst_if                clk_rst_if    (.clk(clk), .rst_n(rst_n));
  rst_shadowed_if           rst_shad_if   (.rst_n(rst_n), .rst_shadowed_n(rst_shadowed_n));
  tl_if                     tl_csr_if     (.clk(clk), .rst_n(rst_n));
  tl_if                     tl_unfilt_if  (.clk(clk), .rst_n(rst_n));
  tl_if                     tl_filt_if    (.clk(clk), .rst_n(rst_n));
  ac_range_check_misc_io_if misc_if       ();

  `DV_ALERT_IF_CONNECT()

  // DUT
  ac_range_check dut (
    .clk_i                    (clk                          ),
    .rst_ni                   (rst_n                        ),
    .rst_shadowed_ni          (rst_shadowed_n               ),
    // Alerts
    .alert_rx_i               (alert_rx                     ),
    .alert_tx_o               (alert_tx                     ),
    // RACL interface
    .racl_policies_i          (misc_if.racl_policies        ),
    .racl_error_o             (misc_if.racl_error           ),
    // Access range check interrupts
    .intr_deny_cnt_reached_o  (intr_deny_cnt_reached        ),
    // Bus interface
    .tl_i                     (tl_csr_if.h2d                ),
    .tl_o                     (tl_csr_if.d2h                ),
    // Inter module signals
    .range_check_overwrite_i  (misc_if.range_check_overwrite),
    // Incoming TLUL interface
    .ctn_tl_h2d_i             (tl_unfilt_if.h2d             ),
    .ctn_tl_d2h_o             (tl_unfilt_if.d2h             ),
    // Filtered outgoing TLUL interface to the target if request is not squashed
    .ctn_filtered_tl_h2d_o    (tl_filt_if.h2d               ),
    .ctn_filtered_tl_d2h_i    (tl_filt_if.d2h               )
  );

  assign interrupts[DenyCntReached] = intr_deny_cnt_reached;

  initial begin
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif", rst_shad_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_csr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.tl_unfilt_agt*", "vif", tl_unfilt_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.tl_filt_agt*", "vif", tl_filt_if);
    uvm_config_db#(misc_vif_t)::set(null, "*.env", "misc_vif", misc_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
