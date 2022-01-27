// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import rv_dm_params_pkg::*;
  import rv_dm_env_pkg::*;
  import rv_dm_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire jtag_tdo_oe;

  // interfaces
  clk_rst_if  clk_rst_if(.clk(clk), .rst_n(rst_n));
  jtag_if     jtag_if();
  tl_if       tl_host_if(.clk(clk), .rst_n(rst_n));
  tl_if       tl_device_if(.clk(clk), .rst_n(rst_n));
  rv_dm_if    rv_dm_if();

  // dut
  rv_dm #(
    .NrHarts      (rv_dm_params_pkg::NR_HARTS),
    .IdcodeValue  (rv_dm_params_pkg::JTAG_ID_CODE)
  ) dut (
    .clk_i        (clk        ),
    .rst_ni       (rst_n      ),

    .testmode_i   (rv_dm_if.testmode    ),
    .ndmreset_o   (rv_dm_if.ndmreset    ),
    .dmactive_o   (rv_dm_if.dmactive    ),
    .debug_req_o  (rv_dm_if.debug_req   ),
    .unavailable_i(rv_dm_if.unavailable ),

    .tl_d_i       (tl_device_if.h2d ),
    .tl_d_o       (tl_device_if.d2h ),

    .tl_h_o       (tl_host_if.h2d   ),
    .tl_h_i       (tl_host_if.d2h   ),

    .jtag_req_i   ({jtag_if.tck, jtag_if.tms, jtag_if.trst_n, jtag_if.tdi}),
    .jtag_rsp_o   ({jtag_if.tdo, jtag_tdo_oe})
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual rv_dm_if)::set(null, "*.env*", "rv_dm_vif", rv_dm_if);
    uvm_config_db#(virtual jtag_if)::set(null, "*.env.m_jtag_agent*", "vif", jtag_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_host_agent*", "vif", tl_host_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_device_agent*", "vif", tl_device_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
