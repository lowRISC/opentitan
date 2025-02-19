// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // Dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import soc_dbg_ctrl_env_pkg::*;
  import soc_dbg_ctrl_test_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire                                    clk;
  wire                                    rst_n;
  wire                                    rst_shadowed_n;
  wire soc_dbg_ctrl_pkg::soc_dbg_policy_t soc_dbg_policy_bus;
  wire lc_ctrl_state_pkg::soc_dbg_state_t soc_dbg_state;
  wire lc_ctrl_pkg::lc_tx_t               lc_dft_en;
  wire lc_ctrl_pkg::lc_tx_t               lc_hw_debug_en;
  wire lc_ctrl_pkg::lc_tx_t               lc_raw_test_rma;
  wire pwrmgr_pkg::pwr_boot_status_t      boot_status;
  wire                                    halt_cpu_boot;
  wire rom_ctrl_pkg::pwrmgr_data_t        continue_cpu_boot;

  // Interfaces
  clk_rst_if      clk_rst_if    (.clk(clk), .rst_n(rst_n));
  rst_shadowed_if rst_shad_if   (.rst_n(rst_n), .rst_shadowed_n(rst_shadowed_n));
  tl_if           tl_csr_if     (.clk(clk), .rst_n(rst_n));
  tl_if           tl_jtag_if    (.clk(clk), .rst_n(rst_n));

  `DV_ALERT_IF_CONNECT()

  // DUT
  soc_dbg_ctrl dut (
    .clk_i                    (clk                    ),
    .rst_ni                   (rst_n                  ),
    .rst_shadowed_ni          (rst_shadowed_n         ),
    // Alerts
    .alert_rx_i               (alert_rx               ),
    .alert_tx_o               (alert_tx               ),
    // TLUL Core interface
    .core_tl_i                (tl_csr_if.h2d          ),
    .core_tl_o                (tl_csr_if.d2h          ),
    // TLUL JTAG interface
    .jtag_tl_i                (tl_jtag_if.h2d         ),
    .jtag_tl_o                (tl_jtag_if.d2h         ),
    // Debug policy distributed to the SoC
    .soc_dbg_policy_bus_o     (soc_dbg_policy_bus     ),
    // LC CTRL broadcast signals
    .soc_dbg_state_i          (soc_dbg_state          ),
    .lc_dft_en_i              (lc_dft_en              ),
    .lc_hw_debug_en_i         (lc_hw_debug_en         ),
    .lc_raw_test_rma_i        (lc_raw_test_rma        ),
    .boot_status_i            (boot_status            ),
    // Boot information from the pwrmgr
    // Halts CPU boot in early lifecycle stages after reset based on an external signal
    // Halt functionality disappears in the production lifecycle
    .halt_cpu_boot_i          (halt_cpu_boot          ),
    .continue_cpu_boot_o      (continue_cpu_boot      )
  );

  // Manage inputs
  // TODO should be driven dynamically by an io_agent (to be created TODO MVy)
  assign soc_dbg_state    = lc_ctrl_state_pkg::SocDbgStBlank;
  assign lc_dft_en        = lc_ctrl_pkg::Off;
  assign lc_hw_debug_en   = lc_ctrl_pkg::Off;
  assign lc_raw_test_rma  = lc_ctrl_pkg::Off;
  assign boot_status      = '0;
  assign halt_cpu_boot    = 1'b1;

  // Manage outputs
  // TODO should be monitored dynamically by an io_agent (to be created TODO MVy)
  // assign io_if.soc_dbg_policy_bus  = soc_dbg_policy_bus;
  // assign io_if.continue_cpu_boot   = continue_cpu_boot;

  initial begin
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env",
                                            "clk_rst_vif_soc_dbg_ctrl_jtag_reg_block", clk_rst_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif", rst_shad_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_*_core*", "vif", tl_csr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_*_jtag*", "vif", tl_jtag_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end
endmodule : tb
