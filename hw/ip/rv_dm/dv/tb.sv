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

  `DV_ALERT_IF_CONNECT()

  // dut
  rv_dm #(
    .IdcodeValue (rv_dm_env_pkg::RV_DM_JTAG_IDCODE)
  ) dut (
    .clk_i                     (clk  ),
    .rst_ni                    (rst_n),
    .clk_lc_i                  (clk_lc  ),
    .rst_lc_ni                 (rst_lc_n),

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

    .jtag_i                    ({jtag_if.tck, jtag_if.tms, jtag_if.trst_n, jtag_if.tdi}),
    .jtag_o                    ({jtag_if.tdo, jtag_tdo_oe})
  );

  initial begin
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
