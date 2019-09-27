// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import ${name}_env_pkg::*;
  import ${name}_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
% if is_cip:
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire [NUM_MAX_ALERTS-1:0] alerts;
% endif

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
% if is_cip:
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(NUM_MAX_ALERTS) alerts_if(alerts);
  pins_if #(1) devmode_if();
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
% endif
% for agent in env_agents:
  ${agent}_if ${agent}_if();
% endfor

  // dut
  ${name} dut (
    .clk_i                (clk        ),
% if is_cip:
    .rst_ni               (rst_n      ),

    .tl_i                 (tl_if.h2d  ),
    .tl_o                 (tl_if.d2h  )

% else:
    .rst_ni               (rst_n      )

% endif
    // TODO: add remaining IOs and hook them
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
% if is_cip:
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(alerts_vif)::set(null, "*.env", "alerts_vif", alerts_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(tlul_assert_vif)::set(null, "*.env", "tlul_assert_vif",
                                         tb.dut.tlul_assert_host);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
% endif
% for agent in env_agents:
    uvm_config_db#(virtual ${agent}_if)::set(null, "*.env.m_${agent}_agent*", "vif", ${agent}_if);
% endfor
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
