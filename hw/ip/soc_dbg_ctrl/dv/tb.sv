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

  // Interfaces
  clk_rst_if              clk_rst_if    (.clk(clk), .rst_n(rst_n));
  rst_shadowed_if         rst_shad_if   (.rst_n(rst_n), .rst_shadowed_n(rst_shadowed_n));
  tl_if                   tl_csr_if     (.clk(clk), .rst_n(rst_n));
  tl_if                   tl_jtag_if    (.clk(clk), .rst_n(rst_n));
  soc_dbg_ctrl_misc_io_if misc_if       ();

  `DV_ALERT_IF_CONNECT()

  // DUT
  soc_dbg_ctrl dut (
    .clk_i                    (clk                        ),
    .rst_ni                   (rst_n                      ),
    .rst_shadowed_ni          (rst_shadowed_n             ),
    // Alerts
    .alert_rx_i               (alert_rx                   ),
    .alert_tx_o               (alert_tx                   ),
    // TLUL Core interface
    .core_tl_i                (tl_csr_if.h2d              ),
    .core_tl_o                (tl_csr_if.d2h              ),
    // TLUL JTAG interface
    .jtag_tl_i                (tl_jtag_if.h2d             ),
    .jtag_tl_o                (tl_jtag_if.d2h             ),
    // Debug policy distributed to the SoC
    .soc_dbg_policy_bus_o     (misc_if.soc_dbg_policy_bus ),
    // LC CTRL broadcast signals
    .soc_dbg_state_i          (misc_if.soc_dbg_state      ),
    .lc_dft_en_i              (misc_if.lc_dft_en          ),
    .lc_hw_debug_en_i         (misc_if.lc_hw_debug_en     ),
    .lc_raw_test_rma_i        (misc_if.lc_raw_test_rma    ),
    .boot_status_i            (misc_if.boot_status        ),
    // Boot information from the pwrmgr
    // Halts CPU boot in early lifecycle stages after reset based on an external signal
    // Halt functionality disappears in the production lifecycle
    .halt_cpu_boot_i          (misc_if.halt_cpu_boot      ),
    .continue_cpu_boot_o      (misc_if.continue_cpu_boot  )
  );

  initial begin
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env",
                                            "clk_rst_vif_soc_dbg_ctrl_jtag_reg_block", clk_rst_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif", rst_shad_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_*_core*", "vif", tl_csr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_*_jtag*", "vif", tl_jtag_if);
    uvm_config_db#(misc_vif_t)::set(null, "*.env", "misc_vif", misc_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end
endmodule : tb
