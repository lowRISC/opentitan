// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import otp_ctrl_env_pkg::*;
  import otp_ctrl_test_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import mem_bkdr_util_pkg::mem_bkdr_util;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // TB base test ENV_T & CFG_T specification
  //
  // Specify the parameters for the otp_ctrl_base_test
  // This will invoke the UVM registry and link this test type to
  // the name 'otp_ctrl_base_test' as a test name passed by UVM_TESTNAME
  //
  // This is done explicitly only for the prim_pkg::ImplGeneric implementation
  // since partner base tests inherit from otp_ctrl_base_test#(CFG_T, ENV_T) and
  // specify directly (CFG_T, ENV_T) via the class extension and use a different
  // UVM_TESTNAME
  if (`PRIM_DEFAULT_IMPL == prim_pkg::ImplGeneric) begin : gen_spec_base_test_params
    typedef otp_ctrl_base_test #(.CFG_T(otp_ctrl_env_cfg),
                                 .ENV_T(otp_ctrl_env)) otp_ctrl_base_test_t;
  end

  wire clk, rst_n;
  wire otp_ctrl_pkg::flash_otp_key_req_t flash_req;
  wire otp_ctrl_pkg::flash_otp_key_rsp_t flash_rsp;
  wire otp_ctrl_pkg::otbn_otp_key_req_t  otbn_req;
  wire otp_ctrl_pkg::otbn_otp_key_rsp_t  otbn_rsp;
  wire otp_ctrl_pkg::sram_otp_key_req_t[NumSramKeyReqSlots-1:0] sram_req;
  wire otp_ctrl_pkg::sram_otp_key_rsp_t[NumSramKeyReqSlots-1:0] sram_rsp;

  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire intr_otp_operation_done, intr_otp_error;

  // Output from close-source OTP, not checked in open-source env.
  wire otp_ctrl_pkg::otp_ast_req_t ast_req;
  wire [7:0] otp_obs_o;

  tlul_pkg::tl_d2h_t prim_tl_o;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);

  // lc_otp interfaces
  push_pull_if #(.HostDataWidth(LC_PROG_DATA_SIZE), .DeviceDataWidth(1))
               lc_prog_if(.clk(clk), .rst_n(rst_n));
  push_pull_if #(.DeviceDataWidth(SRAM_DATA_SIZE))
               sram_if[NumSramKeyReqSlots](.clk(clk), .rst_n(rst_n));
  push_pull_if #(.DeviceDataWidth(OTBN_DATA_SIZE)) otbn_if(.clk(clk), .rst_n(rst_n));
  push_pull_if #(.DeviceDataWidth(FLASH_DATA_SIZE)) flash_addr_if(.clk(clk), .rst_n(rst_n));
  push_pull_if #(.DeviceDataWidth(FLASH_DATA_SIZE)) flash_data_if(.clk(clk), .rst_n(rst_n));

  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  tl_if prim_tl_if(.clk(clk), .rst_n(rst_n));

  otp_ctrl_if otp_ctrl_if(.clk_i(clk), .rst_ni(rst_n));

  `DV_ALERT_IF_CONNECT()

  // edn_clk, edn_rst_n and edn_if are defined and driven in below macro
  `DV_EDN_IF_CONNECT

  assign otp_ctrl_if.lc_prog_req = lc_prog_if.req;
  assign otp_ctrl_if.lc_prog_err = lc_prog_if.d_data;

  // Assign to otp_ctrl_if for assertion checks.
  assign otp_ctrl_if.lc_prog_ack = lc_prog_if.ack;
  assign otp_ctrl_if.flash_acks = flash_data_if.ack;
  assign otp_ctrl_if.otbn_ack  = otbn_if.ack;

  // This signal probes design's alert request to avoid additional logic for triggering alert and
  // disable assertions.
  // Alert checkings are done independently in otp_ctrl's scb.
  // The correctness of this probed signal is checked in otp_ctrl's scb as well.
  assign otp_ctrl_if.alert_reqs = dut.alerts[0] | dut.alerts[1];

  // connected to interface
  wire otp_ext_voltage_h = otp_ctrl_if.ext_voltage_h_io;

  // dut
  otp_ctrl dut (
    .clk_i                      (clk        ),
    .rst_ni                     (rst_n      ),
    // edn
    .clk_edn_i                  (edn_clk    ),
    .rst_edn_ni                 (edn_rst_n  ),
    .edn_o                      (edn_if[0].req ),
    .edn_i                      ({edn_if[0].ack, edn_if[0].d_data}),
    // bus interfaces
    .core_tl_i                  (tl_if.h2d  ),
    .core_tl_o                  (tl_if.d2h  ),
    .prim_tl_i                  (prim_tl_if.h2d),
    .prim_tl_o                  (prim_tl_if.d2h),
    // interrupt
    .intr_otp_operation_done_o  (intr_otp_operation_done),
    .intr_otp_error_o           (intr_otp_error),
    // alert
    .alert_rx_i                 (alert_rx   ),
    .alert_tx_o                 (alert_tx   ),
    // ast
    .obs_ctrl_i                 (otp_ctrl_if.obs_ctrl_i),
    .otp_obs_o                  (otp_obs_o),
    .otp_ast_pwr_seq_o          (ast_req),
    .otp_ast_pwr_seq_h_i        (otp_ctrl_if.otp_ast_pwr_seq_h_i),
    // pwrmgr
    .pwr_otp_i                  (otp_ctrl_if.pwr_otp_init_i),
    .pwr_otp_o                  ({otp_ctrl_if.pwr_otp_done_o, otp_ctrl_if.pwr_otp_idle_o}),
    // lc
    .lc_otp_vendor_test_i       (otp_ctrl_if.otp_vendor_test_ctrl_i),
    .lc_otp_vendor_test_o       (otp_ctrl_if.otp_vendor_test_status_o),
    .lc_otp_program_i           ({lc_prog_if.req, lc_prog_if.h_data}),
    .lc_otp_program_o           ({lc_prog_if.d_data, lc_prog_if.ack}),
    .lc_creator_seed_sw_rw_en_i (otp_ctrl_if.lc_creator_seed_sw_rw_en_i),
    .lc_owner_seed_sw_rw_en_i   (otp_ctrl_if.lc_owner_seed_sw_rw_en_i),
    .lc_seed_hw_rd_en_i         (otp_ctrl_if.lc_seed_hw_rd_en_i),
    .lc_dft_en_i                (otp_ctrl_if.lc_dft_en_i),
    .lc_escalate_en_i           (otp_ctrl_if.lc_escalate_en_i),
    .lc_check_byp_en_i          (otp_ctrl_if.lc_check_byp_en_i),
    .otp_lc_data_o              (otp_ctrl_if.lc_data_o),
    // keymgr
    .otp_keymgr_key_o           (otp_ctrl_if.keymgr_key_o),
    // flash
    .flash_otp_key_i            (flash_req),
    .flash_otp_key_o            (flash_rsp),
    // sram
    .sram_otp_key_i             (sram_req),
    .sram_otp_key_o             (sram_rsp),
    // otbn
    .otbn_otp_key_i             (otbn_req),
    .otbn_otp_key_o             (otbn_rsp),

    .otp_broadcast_o            (otp_ctrl_if.otp_broadcast_o),
    .otp_ext_voltage_h_io       (otp_ext_voltage_h),

    //scan
    .scan_en_i                  (otp_ctrl_if.scan_en_i),
    .scan_rst_ni                (otp_ctrl_if.scan_rst_ni),
    .scanmode_i                 (otp_ctrl_if.scanmode_i),

    // Test-related GPIO output
    .cio_test_o                 (otp_ctrl_if.cio_test_o),
    .cio_test_en_o              (otp_ctrl_if.cio_test_en_o)
  );

  for (genvar i = 0; i < NumSramKeyReqSlots; i++) begin : gen_sram_pull_if
    assign sram_req[i]              = sram_if[i].req;
    assign sram_if[i].ack           = sram_rsp[i].ack;
    assign sram_if[i].d_data        = {sram_rsp[i].key, sram_rsp[i].nonce, sram_rsp[i].seed_valid};
    assign otp_ctrl_if.sram_acks[i] = sram_rsp[i].ack;
    initial begin
      uvm_config_db#(virtual push_pull_if#(.DeviceDataWidth(SRAM_DATA_SIZE)))::set(null,
                     $sformatf("*env.m_sram_pull_agent[%0d]*", i), "vif", sram_if[i]);
    end
  end
  assign otbn_req       = otbn_if.req;
  assign otbn_if.ack    = otbn_rsp.ack;
  assign otbn_if.d_data = {otbn_rsp.key, otbn_rsp.nonce, otbn_rsp.seed_valid};

  assign flash_req            = {flash_data_if.req, flash_addr_if.req};
  assign flash_data_if.ack    = flash_rsp.data_ack;
  assign flash_addr_if.ack    = flash_rsp.addr_ack;
  assign flash_data_if.d_data = {flash_rsp.key, flash_rsp.seed_valid};
  assign flash_addr_if.d_data = {flash_rsp.key, flash_rsp.seed_valid};

  assign interrupts[OtpOperationDone] = intr_otp_operation_done;
  assign interrupts[OtpErr]           = intr_otp_error;

  // Instantitate the memory backdoor util instance only for OS implementation
  // Proprietary IP will instantiate their own backdoor util

  if (`PRIM_DEFAULT_IMPL == prim_pkg::ImplGeneric) begin : gen_impl_generic
    `define MEM_MODULE_PATH \
        tb.dut.u_otp.gen_generic.u_impl_generic.u_prim_ram_1p_adv.gen_ram_inst[0]

    `define MEM_ARRAY_PATH \
        `MEM_MODULE_PATH.u_mem.gen_generic.u_impl_generic.mem

    initial begin : mem_bkdr_util_gen
      mem_bkdr_util m_mem_bkdr_util;
      m_mem_bkdr_util = new(.name("mem_bkdr_util"),
                            .path(`DV_STRINGIFY(`MEM_ARRAY_PATH)),
                            .depth($size(`MEM_ARRAY_PATH)),
                            .n_bits($bits(`MEM_ARRAY_PATH)),
                            .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_22_16));

      uvm_config_db#(mem_bkdr_util)::set(null, "*.env", "mem_bkdr_util", m_mem_bkdr_util);
    end : mem_bkdr_util_gen

    `undef MEM_ARRAY_PATH
    `undef MEM_MODULE_PATH
  end : gen_impl_generic

  // DV forced otp_cmd_i to reach invalid state, thus violate the assertions
  for (genvar idx = 0; idx < NumPart; idx++) begin : gen_assertoff_loop
    if (is_hw_part_idx(idx)) begin : gen_assertoff
      initial begin
        $assertoff(0, tb.dut.gen_partitions[idx].gen_buffered.u_part_buf.OtpErrorState_A);
      end
    end
  end

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env",
                                            "clk_rst_vif_otp_ctrl_prim_reg_block", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_otp_ctrl_core_reg_block*",
                                       "vif", tl_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_otp_ctrl_prim_reg_block",
                                       "vif", prim_tl_if);
    uvm_config_db#(virtual push_pull_if#(.DeviceDataWidth(OTBN_DATA_SIZE)))::set(null,
                   "*env.m_otbn_pull_agent*", "vif", otbn_if);
    uvm_config_db#(virtual push_pull_if#(.DeviceDataWidth(FLASH_DATA_SIZE)))::set(null,
                   "*env.m_flash_data_pull_agent*", "vif", flash_data_if);
    uvm_config_db#(virtual push_pull_if#(.DeviceDataWidth(FLASH_DATA_SIZE)))::set(null,
                   "*env.m_flash_addr_pull_agent*", "vif", flash_addr_if);
    uvm_config_db#(virtual push_pull_if#(.HostDataWidth(LC_PROG_DATA_SIZE), .DeviceDataWidth(1)))::
                   set(null, "*env.m_lc_prog_pull_agent*", "vif", lc_prog_if);

    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);

    uvm_config_db#(virtual otp_ctrl_if)::set(null, "*.env", "otp_ctrl_vif", otp_ctrl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
