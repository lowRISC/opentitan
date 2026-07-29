// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import cheriot_env_pkg::*;
  import cheriot_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  `DV_ALERT_IF_CONNECT()

  // dut
  cheriot dut (
    .clk_i                (clk      ),
    .rst_ni               (rst_n    ),

    // Bus interface (device) for CSRs
    .regs_tl_d_i          (tl_if.h2d),
    .regs_tl_d_o          (tl_if.d2h),

    // Alerts
    .alert_rx_i           (alert_rx ),
    .alert_tx_o           (alert_tx ),

    // Execution mode
    .cheriot_ena_i        (prim_mubi_pkg::MuBi4False),

    // Core data port with its capability tag sideband
    .cored_tl_d_i         (tlul_pkg::TL_H2D_DEFAULT),
    .cored_tag_h2d_i      (1'b0),
    .cored_tl_d_o         (),
    .cored_tag_d2h_o      (),

    // Core revocation bitmap port
    .corerevbm_tl_i       (tlul_pkg::TL_H2D_DEFAULT),
    .corerevbm_tl_o       (),

    // System revocation bitmap window
    .revbm_tl_d_i         (tlul_pkg::TL_H2D_DEFAULT),
    .revbm_tl_d_o         (),

    // Host port towards the interconnect
    .cored_tl_h_o         (),
    .cored_tl_h_i         (tlul_pkg::TL_D2H_DEFAULT),

    // Host port towards the meta SRAM
    .meta_sram_tl_o       (),
    .meta_sram_tl_i       (tlul_pkg::TL_D2H_DEFAULT)
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
