// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import sram_ctrl_pkg::*;
  import sram_ctrl_env_pkg::*;
  import sram_ctrl_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire clk_otp, rst_otp_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // OTP key derivation interface
  otp_ctrl_pkg::sram_otp_key_req_t key_req;
  otp_ctrl_pkg::sram_otp_key_rsp_t key_rsp;

  otp_ctrl_pkg::sram_key_t   key;
  otp_ctrl_pkg::sram_nonce_t nonce;

  wire seed_valid;

  lc_ctrl_pkg::lc_tx_t lc_esc_en;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  clk_rst_if otp_clk_rst_if(.clk(clk_otp), .rst_n(rst_otp_n));
  pins_if #(1) devmode_if(devmode);

  // TLUL interface to the CSR regfile
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  // TLUL interface to the SRAM memory itself
  tl_if sram_tl_if(.clk(clk), .rst_n(rst_n));

  // KDI interface for the OTP<->SRAM connections
  push_pull_if #(.DeviceDataWidth(KDI_DATA_SIZE)) kdi_if(.clk(clk_otp), .rst_n(rst_otp_n));

  // Interface for lifecycle escalation
  sram_ctrl_lc_if lc_if();

  `DV_ALERT_IF_CONNECT

  // DUT
  //
  // Top level parameters for SRAM are:
  // - ADDR_BITS: The number of address bits.
  //              This will be set to 10 for the retention SRAM,
  //              and 14 for the Main SRAM.
  //
  // - WIDTH: width of the SRAM data.
  //          This is set to 32 for both the Main and Retention SRAMS,
  //          but is parameterizable in case we want to test the SRAM variant
  //          used in OTBN.

  sram_ctrl_wrapper #(
    .AddrWidth(`ADDR_BITS),
    .DataWidth(`WIDTH)
  ) dut (
    // main clock
    .clk_i(clk),
    .rst_ni(rst_n),
    // OTP clock
    .clk_otp_i(clk_otp),
    .rst_otp_ni(rst_otp_n),
    // TLUL interface for CSR regfile
    .csr_tl_i(tl_if.h2d),
    .csr_tl_o(tl_if.d2h),
    // TLUL interface for SRAM memory
    .sram_tl_i(sram_tl_if.h2d),
    .sram_tl_o(sram_tl_if.d2h),
    // Alert I/O
    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx),
    // Life cycle escalation
    .lc_escalate_en_i(lc_esc_en),
    // OTP key derivation interface
    .sram_otp_key_o(key_req),
    .sram_otp_key_i(key_rsp)
  );

  // KDI interface assignments
  assign kdi_if.req         = key_req.req;
  assign key_rsp.ack        = kdi_if.ack;
  assign key_rsp.key        = key;
  assign key_rsp.nonce      = nonce;
  assign key_rsp.seed_valid = seed_valid;
  // key, nonce, seed_valid all driven by push_pull Device interface
  assign {key, nonce, seed_valid} = kdi_if.d_data;

  // LC interface assignment
  assign lc_esc_en = lc_if.lc_esc_en;

  // bind mem_bkdr_if
  `define SRAM_CTRL_MEM_HIER \
    dut.u_ram1p_sram.u_prim_ram_1p_adv.u_mem.gen_generic.u_impl_generic
  bind `SRAM_CTRL_MEM_HIER mem_bkdr_if mem_bkdr_if();

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    otp_clk_rst_if.set_active();

    // set interfaces into uvm_config_db
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "otp_clk_rst_vif", otp_clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual push_pull_if#(.DeviceDataWidth(KDI_DATA_SIZE)))::set(null,
      "*.env.m_kdi_agent*", "vif", kdi_if);
    uvm_config_db#(virtual sram_ctrl_lc_if)::set(null, "*.env", "lc_vif", lc_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_sram_tl_agent*", "vif", sram_tl_if);
    uvm_config_db#(mem_bkdr_vif)::set(null, "*.env", "mem_bkdr_vif",
      `SRAM_CTRL_MEM_HIER.mem_bkdr_if);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
