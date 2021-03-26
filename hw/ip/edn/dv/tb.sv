// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import edn_env_pkg::*;
  import edn_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire intr_edn_cmd_req_done, intr_edn_fatal_err;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  edn_pkg::edn_req_t [NUM_ENDPOINTS-1:0] endpoint_req;
  edn_pkg::edn_rsp_t [NUM_ENDPOINTS-1:0] endpoint_rsp;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  csrng_if csrng_if(.clk(clk), .rst_n(rst_n));
  push_pull_if#(.HostDataWidth(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH))
       endpoint_if[NUM_ENDPOINTS-1:0](.clk(clk), .rst_n(rst_n));

  `DV_ALERT_IF_CONNECT

  // dut
  edn#(.NumEndPoints(NUM_ENDPOINTS)) dut (
    .clk_i                     (clk      ),
    .rst_ni                    (rst_n    ),

    .tl_i                      (tl_if.h2d),
    .tl_o                      (tl_if.d2h),

    .edn_i                     (endpoint_req),
    .edn_o                     (endpoint_rsp),

    .csrng_cmd_i               (csrng_if.cmd_rsp),
    .csrng_cmd_o               (csrng_if.cmd_req),

    .alert_rx_i                (alert_rx),
    .alert_tx_o                (alert_tx),

    .intr_edn_cmd_req_done_o   (intr_edn_cmd_req_done),
    .intr_edn_fatal_err_o      (intr_edn_fatal_err)
  );

  for (genvar i = 0; i < NUM_ENDPOINTS; i++) begin : gen_endpoint_if
    assign endpoint_req[i].edn_req = endpoint_if[i].req;
    assign endpoint_if[i].ack = endpoint_rsp[i].edn_ack;
    assign endpoint_if[i].d_data = {endpoint_rsp[i].edn_fips, endpoint_rsp[i].edn_bus};
    initial begin
      uvm_config_db#(virtual push_pull_if#(.HostDataWidth(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)))::
          set(null, $sformatf("*.env.m_endpoint_agent[%0d]*", i),
                     "vif", endpoint_if[i]);
    end
  end

  assign interrupts[CmdReqDone] = intr_edn_cmd_req_done;
  assign interrupts[FifoErr]    = intr_edn_fatal_err;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual csrng_if)::set(null, "*.env.m_csrng_agent*", "vif", csrng_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
