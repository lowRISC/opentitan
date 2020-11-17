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
  wire intr_edn_cmd_req_done, intr_edn_fifo_err;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  push_pull_if#(.DataWidth(GENBITS_BUS_WIDTH))  csrng_if();
  // TODO: add multiple endpoints, generate?
  push_pull_if#(.DataWidth(ENDPOINT_BUS_WIDTH)) endpoint_if[NUM_ENDPOINTS-1:0]();

  // dut
  edn#(.NumEndPoints(NUM_ENDPOINTS)) dut (
    .clk_i                     (clk      ),
    .rst_ni                    (rst_n    ),

    .tl_i                      (tl_if.h2d),
    .tl_o                      (tl_if.d2h),

    // TODO: add multiple endpoints, generate?
    // .edn_i                     ({endpoint_if[NUM_ENDPOINTS-1].req, endpoint_if[0].req}),
    .edn_i                     (endpoint_if[0].req),
    .edn_o                     (),

    .csrng_cmd_i               ('h0),
    .csrng_cmd_o               (),

    .intr_edn_cmd_req_done_o   (intr_edn_cmd_req_done),
    .intr_edn_fifo_err_o       (intr_edn_fifo_err)
  );

  assign interrupts[CmdReqDone] = intr_edn_cmd_req_done;
  assign interrupts[FifoErr]    = intr_edn_fifo_err;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual push_pull_if#(.DataWidth(GENBITS_BUS_WIDTH)))::set(null, "*.env.m_csrng_agent*", "vif", csrng_if);
    // TODO: add multiple endpoints, generate?
    uvm_config_db#(virtual push_pull_if#(.DataWidth(ENDPOINT_BUS_WIDTH)))::set(null, "*.env.m_endpoint_agent*", "vif", endpoint_if[NUM_ENDPOINTS-1]);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
