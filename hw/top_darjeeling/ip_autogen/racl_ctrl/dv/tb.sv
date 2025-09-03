// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  import uvm_pkg::*;
  import dv_utils_pkg::*;

  // Note that the tb itself doesn't really need to import the test package. But we *do* need to
  // make sure that the EDA tool doesn't throw away the package at elaboration time, because we want
  // the classes inside it to exist so that their static variables cause them to be registered with
  // the UVM factory.
  import racl_ctrl_test_pkg::racl_ctrl_base_test;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  localparam int unsigned NumSubscribingIps = 11;
  localparam int unsigned NumExternalSubscribingIps = 1;

  wire clk, rst_n, rst_shadowed_n;
  wire intr_racl_error;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  clk_rst_if                    clk_rst_if  (.clk(clk), .rst_n(rst_n));
  rst_shadowed_if               rst_shad_if (.rst_n(rst_n), .rst_shadowed_n(rst_shadowed_n));
  tl_if                         tl_if       (.clk(clk), .rst_n(rst_n));
  racl_ctrl_policies_if         policies_if ();
  racl_error_log_if             int_err_if  (.clk_i(clk), .rst_ni(rst_n));
  racl_error_log_if             ext_err_if  (.clk_i(clk), .rst_ni(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if     (interrupts);

  assign interrupts[0] = {intr_racl_error};

  // Information about the names of alerts and their indices (used by DV_ALERT_IF_CONNECT to attach
  // interfaces to the ports and register them with the config db)
  localparam int unsigned NUM_ALERTS = 2;
  localparam string       LIST_OF_ALERTS[NUM_ALERTS] = {"fatal_fault", "recov_ctrl_update_err"};

  `DV_ALERT_IF_CONNECT()

  racl_ctrl #(
    .NumSubscribingIps(NumSubscribingIps),
    .NumExternalSubscribingIps(NumExternalSubscribingIps)
  ) dut (
    .clk_i                 (clk                                             ),
    .rst_ni                (rst_n                                           ),
    .rst_shadowed_ni       (rst_shadowed_n                                  ),

    .tl_i                  (tl_if.h2d                                       ),
    .tl_o                  (tl_if.d2h                                       ),

    .alert_rx_i            (alert_rx                                        ),
    .alert_tx_o            (alert_tx                                        ),

    .intr_racl_error_o     (intr_racl_error                                 ),

    .racl_policies_o       (policies_if.policies                            ),
    .racl_error_i          (int_err_if.errors[NumSubscribingIps-1:0]        ),
    .racl_error_external_i (ext_err_if.errors[NumExternalSubscribingIps-1:0])
  );

  initial begin
    import racl_ctrl_env_pkg::racl_ctrl_env_wrapper_cfg;

    automatic racl_ctrl_env_wrapper_cfg wrapper_cfg = new();

    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif", rst_shad_if);

    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);

    wrapper_cfg.num_subscribing_ips          = NumSubscribingIps;
    wrapper_cfg.num_external_subscribing_ips = NumExternalSubscribingIps;
    wrapper_cfg.policies_vif                 = policies_if;
    wrapper_cfg.internal_error_vif           = int_err_if;
    wrapper_cfg.external_error_vif           = ext_err_if;

    uvm_config_db#(racl_ctrl_env_wrapper_cfg)::set(null, "*.env", "wrapper", wrapper_cfg);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
