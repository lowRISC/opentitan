// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import ibex_icache_env_pkg::*;
  import ibex_icache_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  ibex_icache_if ibex_icache_if();
  ibex_mem_intf ibex_mem_intf();

  // dut
  ibex_icache dut (
    .clk_i                (clk        ),
    .rst_ni               (rst_n      )

    // TODO: add remaining IOs and hook them
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual ibex_icache_if)::set(null, "*.env.m_ibex_icache_agent*", "vif", ibex_icache_if);
    uvm_config_db#(virtual ibex_mem_intf)::set(null, "*.env.m_ibex_mem_intf_slave_agent*", "vif", ibex_mem_intf);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
