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
  import mem_bkdr_util_pkg::mem_bkdr_util;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk;
  wire rst_n;
  wire clk_otp;
  wire rst_otp_n = rst_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // OTP key derivation interface
  otp_ctrl_pkg::sram_otp_key_req_t key_req;
  otp_ctrl_pkg::sram_otp_key_rsp_t key_rsp;

  otp_ctrl_pkg::sram_key_t   key;
  otp_ctrl_pkg::sram_nonce_t nonce;

  wire seed_valid;

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

  // Interface for SRAM execution
  sram_ctrl_exec_if exec_if();

  `DV_ALERT_IF_CONNECT

  // DUT

  // The exact number of address bits.
  // Will be set to 10 for retention SRAM and 14 for main SRAM.
`ifndef SRAM_ADDR_WIDTH
  `define SRAM_ADDR_WIDTH 32
`endif

  sram_ctrl #(
    // memory size in bytes
    .MemSizeRam(4 * 2 ** `SRAM_ADDR_WIDTH)
  ) dut (
    // main clock
    .clk_i               (clk                 ),
    .rst_ni              (rst_n               ),
    // OTP clock
    .clk_otp_i           (clk_otp             ),
    .rst_otp_ni          (rst_otp_n           ),
    // TLUL interface for CSR regfile
    .ram_tl_i            (sram_tl_if.h2d      ),
    .ram_tl_o            (sram_tl_if.d2h      ),
    // TLUL interface for CSR regfile
    .regs_tl_i           (tl_if.h2d           ),
    .regs_tl_o           (tl_if.d2h           ),
    // Alert I/O
    .alert_rx_i          (alert_rx            ),
    .alert_tx_o          (alert_tx            ),
    // Life cycle escalation
    .lc_escalate_en_i    (lc_if.lc_esc_en     ),
    // OTP key derivation interface
    .sram_otp_key_o      (key_req             ),
    .sram_otp_key_i      (key_rsp             ),
    // SRAM ifetch interface
    .lc_hw_debug_en_i    (exec_if.lc_hw_debug_en    ),
    .otp_en_sram_ifetch_i(exec_if.otp_en_sram_ifetch),
    .cfg_i               ('0                 )
  );

  // KDI interface assignments
  assign kdi_if.req         = key_req.req;
  assign key_rsp.ack        = kdi_if.ack;
  assign key_rsp.key        = key;
  assign key_rsp.nonce      = nonce;
  assign key_rsp.seed_valid = seed_valid;
  // key, nonce, seed_valid all driven by push_pull Device interface
  assign {key, nonce, seed_valid} = kdi_if.d_data;

  // Instantitate the memory backdoor util instance.
  `define SRAM_CTRL_MEM_HIER \
      tb.dut.u_prim_ram_1p_scr.u_prim_ram_1p_adv.u_mem.gen_generic.u_impl_generic.mem

  initial begin
    mem_bkdr_util m_mem_bkdr_util;
    m_mem_bkdr_util = new(.name  ("mem_bkdr_util"),
                          .path  (`DV_STRINGIFY(`SRAM_CTRL_MEM_HIER)),
                          .depth ($size(`SRAM_CTRL_MEM_HIER)),
                          .n_bits($bits(`SRAM_CTRL_MEM_HIER)),
                          .err_detection_scheme(mem_bkdr_util_pkg::ParityOdd));

    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    otp_clk_rst_if.set_active(.drive_rst_n_val(1'b0));

    // set interfaces into uvm_config_db
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "otp_clk_rst_vif", otp_clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual push_pull_if#(.DeviceDataWidth(KDI_DATA_SIZE)))::set(null,
      "*.env.m_kdi_agent*", "vif", kdi_if);
    uvm_config_db#(virtual sram_ctrl_lc_if)::set(null, "*.env", "lc_vif", lc_if);
    uvm_config_db#(virtual sram_ctrl_exec_if)::set(null, "*.env", "exec_vif", exec_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_sram_tl_agent*", "vif", sram_tl_if);
    uvm_config_db#(mem_bkdr_util)::set(null, "*.env", "mem_bkdr_util", m_mem_bkdr_util);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  `undef SRAM_CTRL_MEM_HIER

endmodule
