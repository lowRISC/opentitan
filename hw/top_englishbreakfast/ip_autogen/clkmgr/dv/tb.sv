// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import clkmgr_env_pkg::*;
  import clkmgr_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // clock interfaces
  wire clk, rst_n, rst_shadowed_n;
  clk_rst_if clk_rst_if (
    .clk  (clk),
    .rst_n(rst_n)
  );

  wire clk_aon, rst_aon_n;
  clk_rst_if aon_clk_rst_if (
    .clk  (clk_aon),
    .rst_n(rst_aon_n)
  );

  wire clk_io, rst_io_n;
  clk_rst_if io_clk_rst_if (
    .clk  (clk_io),
    .rst_n(rst_io_n)
  );

  wire clk_main, rst_main_n;
  clk_rst_if main_clk_rst_if (
    .clk  (clk_main),
    .rst_n(rst_main_n)
  );

  wire clk_usb, rst_usb_n;
  clk_rst_if usb_clk_rst_if (
    .clk  (clk_usb),
    .rst_n(rst_usb_n)
  );

  wire rst_io_div4_n;
  clk_rst_if io_div4_clk_rst_if (
    .clk  (),
    .rst_n(rst_io_div4_n)
  );
  clk_rst_if root_main_clk_rst_if (
    .clk  (),
    .rst_n(rst_root_main_n)
  );
  clk_rst_if root_io_clk_rst_if (
    .clk  (),
    .rst_n(rst_root_io_n)
  );
  clk_rst_if root_io_div4_clk_rst_if (
    .clk  (),
    .rst_n(rst_root_io_div4_n)
  );
  clk_rst_if root_usb_clk_rst_if (
    .clk  (),
    .rst_n(rst_root_usb_n)
  );
  tl_if tl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );

  // The clkmgr interface.
  clkmgr_if clkmgr_if (
    .clk(clk),
    .rst_n(rst_n),
    .rst_aon_n(rst_aon_ni),
    .rst_io_n(rst_io_ni),
    .rst_main_n(rst_main_ni),
    .rst_usb_n(rst_usb_ni)
  );

  // The registers are in the primary partition of the clkmgr.
  bind clkmgr_part_primary clkmgr_csrs_if clkmgr_csrs_if (
    .clk(clk_i),
    .recov_err_csr({
        u_reg.u_recov_err_code_usb_timeout_err.qs,
        u_reg.u_recov_err_code_main_timeout_err.qs,
        u_reg.u_recov_err_code_io_div4_timeout_err.qs,
        u_reg.u_recov_err_code_io_timeout_err.qs,
        u_reg.u_recov_err_code_usb_measure_err.qs,
        u_reg.u_recov_err_code_main_measure_err.qs,
        u_reg.u_recov_err_code_io_div4_measure_err.qs,
        u_reg.u_recov_err_code_io_measure_err.qs,
        u_reg.u_recov_err_code_shadow_update_err.qs
    }),
    .fatal_err_csr({
        u_reg.u_fatal_err_code_shadow_storage_err.qs,
        u_reg.u_fatal_err_code_idle_cnt.qs,
        u_reg.u_fatal_err_code_reg_intg.qs
     }),
    .clk_enables({
        reg2hw.clk_enables.clk_usb_peri_en.q,
        reg2hw.clk_enables.clk_io_peri_en.q,
        reg2hw.clk_enables.clk_io_div4_peri_en.q}),
    .clk_hints({
        reg2hw.clk_hints.clk_main_otbn_hint.q,
        reg2hw.clk_hints.clk_main_kmac_hint.q,
        reg2hw.clk_hints.clk_main_hmac_hint.q,
        reg2hw.clk_hints.clk_main_aes_hint.q})
  );

  rst_shadowed_if rst_shadowed_if (
    .rst_n(rst_n),
    .rst_shadowed_n(rst_shadowed_n)
  );

  initial begin
    // Clocks must be set to active at time 0. The rest of the clock configuration happens
    // in clkmgr_base_vseq.sv.
    clk_rst_if.set_active();
    aon_clk_rst_if.set_active();
    io_clk_rst_if.set_active();
    main_clk_rst_if.set_active();
    usb_clk_rst_if.set_active();
    io_div4_clk_rst_if.set_active();
    root_main_clk_rst_if.set_active();
    root_io_clk_rst_if.set_active();
    root_io_div4_clk_rst_if.set_active();
    root_usb_clk_rst_if.set_active();
  end

  `DV_ALERT_IF_CONNECT()

  // The DUT is the two partitions of the clock manager, connected the same as a top connects them
  // when both are in the same power domain.
  clkmgr_pkg::intraip_s2p_t intraip_s2p;
  clkmgr_pkg::intraip_p2s_t intraip_p2s;
  clkmgr_pkg::clkmgr_out_primary_t clocks_primary;
  clkmgr_pkg::clkmgr_out_secondary_t clocks_secondary;

  clkmgr_part_primary dut_primary (
    .clk_i(clk),
    .rst_ni(rst_n),
    .rst_shadowed_ni(rst_shadowed_n),

    .clk_main_i (clk_main),
    .clk_io_i (clk_io),
    .clk_usb_i (clk_usb),
    .rst_aon_ni(rst_aon_n),
    .rst_io_ni(rst_io_n),
    .rst_main_ni(rst_main_n),
    .rst_usb_ni(rst_usb_n),
    .rst_io_div4_ni(rst_io_div4_n),
    // ICEBOX(#17934): differentiate the root resets as mentioned for rst_io_ni above.
    .rst_root_ni(rst_root_io_n),
    .rst_root_main_ni(rst_root_main_n),
    .rst_root_io_ni(rst_root_io_n),
    .rst_root_io_div4_ni(rst_root_io_div4_n),
    .rst_root_usb_ni(rst_root_usb_n),

    .tl_i(tl_if.h2d),
    .tl_o(tl_if.d2h),

    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx),

    .idle_i    (clkmgr_if.idle_i),

    .lc_hw_debug_en_i(clkmgr_if.lc_hw_debug_en_i),
    .all_clk_byp_req_o(clkmgr_if.all_clk_byp_req),
    .all_clk_byp_ack_i(clkmgr_if.all_clk_byp_ack),
    .io_clk_byp_req_o(clkmgr_if.io_clk_byp_req),
    .io_clk_byp_ack_i(clkmgr_if.io_clk_byp_ack),
    .lc_clk_byp_req_i(clkmgr_if.lc_clk_byp_req),
    .lc_clk_byp_ack_o(clkmgr_if.lc_clk_byp_ack),
    .div_step_down_req_i(clkmgr_if.div_step_down_req),
    .hi_speed_sel_o(clkmgr_if.hi_speed_sel),
    .calib_rdy_i(clkmgr_if.calib_rdy),

    .cg_en_o(),

    .jitter_en_o(clkmgr_if.jitter_en_o),
    .clocks_o   (clocks_primary),

    .intraip_s2p_i(intraip_s2p),
    .intraip_p2s_o(intraip_p2s)
  );

  clkmgr_part_secondary dut_secondary (
    .clk_aon_i (clk_aon),
    .rst_aon_ni(rst_aon_n),

    .pwr_i(clkmgr_if.pwr_i),
    .pwr_o(clkmgr_if.pwr_o),
    .main_pd_aon_clk_en_i(clkmgr_if.main_pd_aon_clk_en),

    .scanmode_i(clkmgr_if.scanmode_i),

    .clocks_secondary_o(clocks_secondary),

    .intraip_s2p_o(intraip_s2p),
    .intraip_p2s_i(intraip_p2s)
  );

  // clkmgr_if presents the clocks of both partitions as one struct.
  assign clkmgr_if.clocks_primary = clocks_primary;
  assign clkmgr_if.clocks_secondary = clocks_secondary;

  initial begin
    // Register interfaces with uvm.
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "aon_clk_rst_vif", aon_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "io_clk_rst_vif", io_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "main_clk_rst_vif", main_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "usb_clk_rst_vif", usb_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "io_div4_clk_rst_vif",
                                            io_div4_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "root_main_clk_rst_vif",
                                            root_main_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "root_io_clk_rst_vif",
                                            root_io_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "root_io_div4_clk_rst_vif",
                                            root_io_div4_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "root_usb_clk_rst_vif",
                                            root_usb_clk_rst_if);
    uvm_config_db#(virtual clkmgr_if)::set(null, "*.env", "clkmgr_vif", clkmgr_if);

    uvm_config_db#(virtual clkmgr_csrs_if)::set(null, "*.env", "clkmgr_csrs_vif",
                                                dut_primary.clkmgr_csrs_if);

    // FIXME Un-comment this once interrupts are created for this ip.
    // uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);

    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif",
                                                 rst_shadowed_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
