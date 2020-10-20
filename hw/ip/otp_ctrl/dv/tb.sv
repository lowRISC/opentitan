// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import otp_ctrl_env_pkg::*;
  import otp_ctrl_test_pkg::*;
  import push_pull_agent_pkg::*;
  import otp_ctrl_reg_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire [3:0] lc_provision_en, lc_dft_en;

  wire [2:0] pwr_otp;
  wire otp_ctrl_pkg::flash_otp_key_req_t flash_req;
  wire otp_ctrl_pkg::flash_otp_key_rsp_t flash_rsp;
  wire otp_ctrl_pkg::otbn_otp_key_req_t  otbn_req;
  wire otp_ctrl_pkg::otbn_otp_key_rsp_t  otbn_rsp;
  wire otp_ctrl_pkg::sram_otp_key_req_t[NumSramKeyReqSlots-1:0] sram_req;
  wire otp_ctrl_pkg::sram_otp_key_rsp_t[NumSramKeyReqSlots-1:0] sram_rsp;

  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire intr_otp_operation_done, intr_otp_error;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  push_pull_if #(SRAM_DATA_SIZE) sram_if[NumSramKeyReqSlots] (.clk(clk), .rst_n(rst_n));
  push_pull_if #(OTBN_DATA_SIZE) otbn_if(.clk(clk), .rst_n(rst_n));
  push_pull_if #(FLASH_DATA_SIZE) flash_addr_if(.clk(clk), .rst_n(rst_n));
  push_pull_if #(FLASH_DATA_SIZE) flash_data_if(.clk(clk), .rst_n(rst_n));
  // TODO: use standard req/rsp agent
  pins_if #(3) pwr_otp_if(pwr_otp);
  pins_if #(4) lc_provision_en_if(lc_provision_en);
  pins_if #(4) lc_dft_en_if(lc_dft_en);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  // dut
  otp_ctrl dut (
    .clk_i                     (clk        ),
    .rst_ni                    (rst_n      ),

    .tl_i                      (tl_if.h2d  ),
    .tl_o                      (tl_if.d2h  ),
    // interrupt
    .intr_otp_operation_done_o (intr_otp_operation_done),
    .intr_otp_error_o          (intr_otp_error),
    // alert
    .alert_rx_i                ('0),
    .alert_tx_o                (  ),
    // ast
    .otp_ast_pwr_seq_o         (  ),
    .otp_ast_pwr_seq_h_i       ('0),
    // edn
    .otp_edn_o                 (  ),
    .otp_edn_i                 ('1),
    // pwrmgr
    .pwr_otp_i                 (pwr_otp[0]),
    .pwr_otp_o                 (pwr_otp[2:1]),
    // lc
    .lc_otp_program_i          ('0),
    .lc_otp_program_o          (  ),
    .lc_otp_token_i            ('0),
    .lc_otp_token_o            (  ),
    .lc_escalate_en_i          (lc_ctrl_pkg::Off),
    .lc_provision_en_i         (lc_provision_en),
    .lc_dft_en_i               (lc_dft_en),
    .otp_lc_data_o             (  ),
    // keymgr
    .otp_keymgr_key_o          (  ),
    // flash
    .flash_otp_key_i           (flash_req),
    .flash_otp_key_o           (flash_rsp),
    // sram
    .sram_otp_key_i            (sram_req),
    .sram_otp_key_o            (sram_rsp),
    // otbn
    .otbn_otp_key_i            (otbn_req),
    .otbn_otp_key_o            (otbn_rsp),

    .hw_cfg_o                  (  )
  );

  for (genvar i = 0; i < NumSramKeyReqSlots; i++) begin : gen_sram_pull_if
    assign sram_req[i]     = sram_if[i].req;
    assign sram_if[i].ack  = sram_rsp[i].ack;
    assign sram_if[i].data = {sram_rsp[i].key, sram_rsp[i].nonce, sram_rsp[i].seed_valid};
    initial begin
      uvm_config_db#(virtual push_pull_if#(SRAM_DATA_SIZE))::set(null,
                     $sformatf("*env.m_sram_pull_agent[%0d]*", i), "vif", sram_if[i]);
    end
  end
  assign otbn_req     = otbn_if.req;
  assign otbn_if.ack  = otbn_rsp.ack;
  assign otbn_if.data = {otbn_rsp.key, otbn_rsp.nonce, otbn_rsp.seed_valid};

  assign flash_req          = {flash_data_if.req, flash_addr_if.req};
  assign flash_data_if.ack  = flash_rsp.data_ack;
  assign flash_addr_if.ack  = flash_rsp.addr_ack;
  assign flash_data_if.data = {flash_rsp.key, flash_rsp.seed_valid};
  assign flash_addr_if.data = {flash_rsp.key, flash_rsp.seed_valid};

  // bind mem_bkdr_if
  `define OTP_CTRL_MEM_HIER \
      dut.u_otp.gen_generic.u_impl_generic.i_prim_ram_1p_adv.u_mem.gen_generic.u_impl_generic

  assign interrupts[OtpOperationDone] = intr_otp_operation_done;
  assign interrupts[OtpErr]           = intr_otp_error;

  bind `OTP_CTRL_MEM_HIER mem_bkdr_if mem_bkdr_if();

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual push_pull_if#(OTBN_DATA_SIZE))::set(null,
                   "*env.m_otbn_pull_agent*", "vif", otbn_if);
    uvm_config_db#(virtual push_pull_if#(FLASH_DATA_SIZE))::set(null,
                   "*env.m_flash_data_pull_agent*", "vif", flash_data_if);
    uvm_config_db#(virtual push_pull_if#(FLASH_DATA_SIZE))::set(null,
                   "*env.m_flash_addr_pull_agent*", "vif", flash_addr_if);

    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(pwr_otp_vif)::set(null, "*.env", "pwr_otp_vif", pwr_otp_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(lc_provision_en_vif)::set(null, "*.env", "lc_provision_en_vif",
                                             lc_provision_en_if);
    uvm_config_db#(lc_dft_en_vif)::set(null, "*.env", "lc_dft_en_vif", lc_dft_en_if);
    uvm_config_db#(mem_bkdr_vif)::set(null, "*.env", "mem_bkdr_vif", `OTP_CTRL_MEM_HIER.mem_bkdr_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  `undef OTP_CTRL_MEM_HIER
endmodule
