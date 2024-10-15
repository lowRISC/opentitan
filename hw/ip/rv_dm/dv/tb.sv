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

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n, clk_lc, rst_lc_n;
  wire jtag_tdo_oe;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  clk_rst_if clk_lc_rst_if (.clk(clk_lc), .rst_n(rst_lc_n));
  tl_if regs_tl_if(.clk(clk), .rst_n(rst_n));
  tl_if mem_tl_if(.clk(clk), .rst_n(rst_n));
  tl_if sba_tl_if(.clk(clk), .rst_n(rst_n));
  jtag_if jtag_if();
  rv_dm_if rv_dm_if(.clk(clk), .rst_n(rst_n));

  // Used for JTAG DTM connections via TL-UL.
  tlul_pkg::tl_h2d_t dbg_tl_h2d;
  tlul_pkg::tl_d2h_t dbg_tl_d2h;

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
    .scan_rst_ni (rv_dm_if.scan_rst_n),
    .scanmode_i  (rv_dm_if.scanmode),
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

    // We don't currently model systems with multiple debug modules. Tie this port off with the same
    // value as given as a default for next_dm_addr in rv_dm.hjson.
    .next_dm_addr_i            ('0),

    .lc_hw_debug_en_i          (rv_dm_if.lc_hw_debug_en           ),
    .pinmux_hw_debug_en_i      (rv_dm_if.pinmux_hw_debug_en       ),
    .lc_dft_en_i               (rv_dm_if.lc_dft_en                ),
    .otp_dis_rv_dm_late_debug_i(rv_dm_if.otp_dis_rv_dm_late_debug ),

    .scanmode_i                (rv_dm_if.scanmode      ),
    .scan_rst_ni               (rv_dm_if.scan_rst_n    ),
    .ndmreset_req_o            (rv_dm_if.ndmreset_req  ),
    .dmactive_o                (rv_dm_if.dmactive      ),
    .debug_req_o               (rv_dm_if.debug_req     ),
    .unavailable_i             (rv_dm_if.unavailable   ),

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

  // Apply the muxing that we get in rv_dm, where the JTAG interface that actually connects to the
  // debug module has direct clock/reset in scan mode, and is disabled if debug is not enabled.
  jtag_mon_if mon_jtag_if ();
`ifndef USE_DMI_INTERFACE
  assign mon_jtag_if.tck    = dut.gen_jtag_gating.dap.tck_i;
  assign mon_jtag_if.trst_n = dut.gen_jtag_gating.dap.trst_ni;
  assign mon_jtag_if.tms    = dut.gen_jtag_gating.dap.tms_i;
  assign mon_jtag_if.tdi    = dut.gen_jtag_gating.dap.td_i;
  assign mon_jtag_if.tdo    = dut.gen_jtag_gating.dap.td_o;
`endif

  initial begin
    // Copy the clock period from clk_rst_if to clk_lc_rst_if. The clock isn't actually connected to
    // anything in the design, but we have DV code that asserts the reset and then waits a cycle
    // before de-asserting it, so the clock must be running.
    clk_lc_rst_if.set_period_ps(clk_rst_if.clk_period_ps);

    clk_rst_if.set_active();
    clk_lc_rst_if.set_active();

    uvm_config_db#(virtual rv_dm_if)::set(null, "*.env", "rv_dm_vif", rv_dm_if);

    // Connect the clk/rst and TL interfaces that apply to the main memory model. These get
    // retrieved in dv_base_env::build_phase.
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_sba_agent*", "vif", sba_tl_if);

    // The clk/rst interface used for clk_lc_i and rst_lc_ni
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env",
                                            "clk_lc_rst_vif", clk_lc_rst_if);

    // Similarly, connect clk/rst/TL for regs_reg_block
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env",
                                            "clk_rst_vif_rv_dm_regs_reg_block", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_rv_dm_regs_reg_block*",
                                       "vif", regs_tl_if);

    // Similarly, connect clk/rst/TL for mem_reg_block
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env",
                                            "clk_rst_vif_rv_dm_mem_reg_block", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_rv_dm_mem_reg_block*",
                                       "vif", mem_tl_if);

    // Connect the JTAG interface, which is used by the jtag_agent build_phase
    uvm_config_db#(virtual jtag_if)::set(null, "*.env.m_jtag_agent", "vif", jtag_if);
    uvm_config_db#(virtual jtag_mon_if)::set(null, "*.env.m_jtag_agent", "mon_vif", mon_jtag_if);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  // Disable TLUL host SBA assertions when injecting intg errors on the response channel.
  initial begin
    forever @rv_dm_if.disable_tlul_assert_host_sba_resp_svas begin
      if (rv_dm_if.disable_tlul_assert_host_sba_resp_svas) begin
        $assertoff(0, dut.tlul_assert_host_sba.gen_host.respOpcode_M);
        $assertoff(0, dut.tlul_assert_host_sba.gen_host.respSzEqReqSz_M);
      end else begin
        $asserton(0, dut.tlul_assert_host_sba.gen_host.respOpcode_M);
        $asserton(0, dut.tlul_assert_host_sba.gen_host.respSzEqReqSz_M);
      end
    end
  end

endmodule
