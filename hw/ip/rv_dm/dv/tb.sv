// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import rv_dm_env_pkg::*;
  import rv_dm_test_pkg::*;
  import top_racl_pkg::*;
  import rv_dm_reg_pkg::NrHarts;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n, clk_lc, rst_lc_n;
  wire jtag_tdo_oe;
  racl_policy_vec_t racl_policies;
  assign racl_policies = 0; // Not currently used

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  clk_rst_if clk_lc_rst_if (.clk(clk_lc), .rst_n(rst_lc_n));
  tl_if regs_tl_if(.clk(clk), .rst_n(rst_n));
  tl_if mem_tl_if(.clk(clk), .rst_n(rst_n));
  tl_if sba_tl_if(.clk(clk), .rst_n(rst_n));
  jtag_if jtag_if();
  rv_dm_mode_if mode_if(.clk(clk));

  // Used for JTAG DTM connections via TL-UL.
  tlul_pkg::tl_h2d_t dbg_tl_h2d;
  tlul_pkg::tl_d2h_t dbg_tl_d2h;

  // The following wires are connected to a bound-in rv_dm_if below
  wire               scan_rst_n, ndmreset_req, dmactive;
  wire [NrHarts-1:0] debug_req, unavailable;

  `DV_ALERT_IF_CONNECT()

`ifdef USE_DMI_INTERFACE
  // Helper module to translate JTAG -> TL-UL requests.
  // TODO: In the long term this JTAG agent should probably be replaced by a TL-UL agent.
  tlul_jtag_dtm #(
    .IdcodeValue(rv_dm_env_pkg::RV_DM_JTAG_IDCODE)
  ) u_tlul_jtag_dtm (
    .clk_i       (clk),
    .rst_ni      (rst_n),
    .jtag_i      ({jtag_if.tck, jtag_if.tms, jtag_if.trst_n, jtag_if.tdi}),
    .jtag_o      ({jtag_if.tdo, jtag_tdo_oe}),
    .scan_rst_ni (scan_rst_n),
    .scanmode_i  (mode_if.scanmode),
    .tl_h2d_o    (dbg_tl_h2d),
    .tl_d2h_i    (dbg_tl_d2h)
  );
`else
  assign dbg_tl_h2d = tlul_pkg::TL_H2D_DEFAULT;
`endif

  // dut
  rv_dm #(
    .IdcodeValue (rv_dm_env_pkg::RV_DM_JTAG_IDCODE),
`ifdef USE_DMI_INTERFACE
    .UseDmiInterface(1'b1)
`else
    .UseDmiInterface(1'b0)
`endif
  ) dut (
    .clk_i                     (clk  ),
    .rst_ni                    (rst_n),
    .clk_lc_i                  (clk_lc  ),
    .rst_lc_ni                 (rst_lc_n),

    .racl_policies_i           (racl_policies),
    .racl_error_o              (),

    .next_dm_addr_i            (mode_if.next_dm_addr            ),
    .lc_hw_debug_clr_i         (mode_if.lc_hw_debug_clr         ),
    .lc_hw_debug_en_i          (mode_if.lc_hw_debug_en          ),
    .lc_dft_en_i               (mode_if.lc_dft_en               ),
    .pinmux_hw_debug_en_i      (mode_if.pinmux_hw_debug_en      ),
    .lc_check_byp_en_i         (mode_if.lc_check_byp_en         ),
    .lc_escalate_en_i          (mode_if.lc_escalate_en          ),
    .lc_init_done_i            (mode_if.lc_init_done            ),
    .strap_en_i                (mode_if.strap_en                ),
    .strap_en_override_i       (mode_if.strap_en_override       ),
    .otp_dis_rv_dm_late_debug_i(mode_if.otp_dis_rv_dm_late_debug),
    .scanmode_i                (mode_if.scanmode                ),

    .scan_rst_ni               (scan_rst_n),
    .ndmreset_req_o            (ndmreset_req),
    .dmactive_o                (dmactive),
    .debug_req_o               (debug_req),
    .unavailable_i             (unavailable),

    .regs_tl_d_i               (regs_tl_if.h2d),
    .regs_tl_d_o               (regs_tl_if.d2h),

    .mem_tl_d_i                (mem_tl_if.h2d),
    .mem_tl_d_o                (mem_tl_if.d2h),

    .sba_tl_h_o                (sba_tl_if.h2d),
    .sba_tl_h_i                (sba_tl_if.d2h),

    .alert_rx_i                (alert_rx ),
    .alert_tx_o                (alert_tx ),

`ifdef USE_DMI_INTERFACE
    .jtag_i                    ('0),
    .jtag_o                    (),
`else
    .jtag_i                    ({jtag_if.tck, jtag_if.tms, jtag_if.trst_n, jtag_if.tdi}),
    .jtag_o                    ({jtag_if.tdo, jtag_tdo_oe}),
`endif

    .dbg_tl_d_i                (dbg_tl_h2d),
    .dbg_tl_d_o                (dbg_tl_d2h)
  );

  // Bind an instance of rv_dm_if into the dut (so that it can figure out hierarchical paths inside
  // the dut).
  //
  // After binding in the interface, use continuous assignments to connect its wires to
  // equivalently- named wires, which are connected to ports of the dut. Because the interface is in
  // active mode, two of these ports (scan_rst_n, unavailable) are driven by the interface. The rest
  // are driven by the dut.
  bind dut rv_dm_if u_rv_dm_if(.clk(clk_i), .rst_n(rst_ni));

  assign scan_rst_n  = dut.u_rv_dm_if.scan_rst_n;
  assign unavailable = dut.u_rv_dm_if.unavailable;

  assign dut.u_rv_dm_if.ndmreset_req = ndmreset_req;
  assign dut.u_rv_dm_if.dmactive     = dmactive;
  assign dut.u_rv_dm_if.debug_req    = debug_req;

  jtag_mon_if mon_jtag_if ();
`ifdef USE_DMI_INTERFACE
  // TODO: In this case, what should the monitor see? Perhaps there should be no JTAG signaling
  // and thus no monitor, but presently the vseqs depend upon the monitor directly.
`else
  // Apply the muxing that we get in rv_dm, where the JTAG interface that actually connects to the
  // debug module has direct clock/reset in scan mode, and is disabled if debug is not enabled.
  assign mon_jtag_if.tck    = dut.gen_jtag_gating.dap.tck_i;
  assign mon_jtag_if.trst_n = dut.gen_jtag_gating.dap.trst_ni;
  assign mon_jtag_if.tms    = dut.gen_jtag_gating.dap.tms_i;
  assign mon_jtag_if.tdi    = dut.gen_jtag_gating.dap.td_i;
  assign mon_jtag_if.tdo    = dut.gen_jtag_gating.dap.td_o;
`endif

  initial begin
    rv_dm_env_cfg cfg;

    // Copy the clock period from clk_rst_if to clk_lc_rst_if. The clock isn't actually connected to
    // anything in the design, but we have DV code that asserts the reset and then waits a cycle
    // before de-asserting it, so the clock must be running.
    clk_lc_rst_if.set_period_ps(clk_rst_if.clk_period_ps);

    clk_rst_if.set_active();
    clk_lc_rst_if.set_active();

    cfg = rv_dm_env_cfg::type_id::create("cfg");
    cfg.rv_dm_vif = dut.u_rv_dm_if;
    cfg.clk_rst_vif = clk_rst_if;
    cfg.clk_rst_vifs["rv_dm_regs_reg_block"] = clk_rst_if;
    cfg.clk_rst_vifs["rv_dm_mem_reg_block"]  = clk_rst_if;
    cfg.clk_lc_rst_vif = clk_lc_rst_if;

    cfg.m_mode_agent_cfg.vif = mode_if;

    cfg.initialize();

    cfg.m_jtag_agent_cfg.vif     = jtag_if;
    cfg.m_jtag_agent_cfg.mon_vif = mon_jtag_if;

    cfg.m_tl_agent_cfgs["rv_dm_regs_reg_block"].vif = regs_tl_if;
    cfg.m_tl_agent_cfgs["rv_dm_mem_reg_block"].vif = mem_tl_if;

    cfg.m_tl_sba_agent_cfg.vif = sba_tl_if;

    uvm_config_db#(rv_dm_env_cfg)::set(null, "*.env", "cfg", cfg);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
