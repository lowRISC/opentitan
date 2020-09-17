// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import tl_agent_env_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  clk_rst_if clk_rst_if(.clk, .rst_n);
  tl_if tl_host_if(.clk, .rst_n);
  tl_if tl_device_if(.clk, .rst_n);

  assign tl_device_if.h2d = tl_host_if.h2d;
  assign tl_host_if.d2h   = tl_device_if.d2h;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env*", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.host_agent*", "vif", tl_host_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.device_agent*", "vif", tl_device_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
