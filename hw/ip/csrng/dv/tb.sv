// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import csrng_env_pkg::*;
  import csrng_test_pkg::*;
  import prim_mubi_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire   clk, rst_n, devmode;
  wire   intr_cmd_req_done;
  wire   intr_entropy_req;
  wire   intr_hw_inst_exc;
  wire   intr_cs_fatal_err;
  wire[NUM_MAX_INTERRUPTS-1:0]              interrupts;
  wire[MuBi8Width - 1:0]                    otp_en_cs_sw_app_read;
  wire[MuBi4Width - 1:0]                    lc_hw_debug_en;
  csrng_pkg::csrng_req_t[NUM_HW_APPS-1:0]   csrng_cmd_req;
  csrng_pkg::csrng_rsp_t[NUM_HW_APPS-1:0]   csrng_cmd_rsp;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if#(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if#(1) devmode_if(devmode);
  pins_if#(MuBi8Width) otp_en_cs_sw_app_read_if(otp_en_cs_sw_app_read);
  pins_if#(MuBi4Width) lc_hw_debug_en_if(lc_hw_debug_en);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  csrng_if  csrng_if[NUM_HW_APPS](.clk(clk), .rst_n(rst_n));
  push_pull_if#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))
      entropy_src_if(.clk(clk), .rst_n(rst_n));
  push_pull_if#(.HostDataWidth(1))   aes_halt_if(.clk(clk), .rst_n(rst_n));
  csrng_path_if csrng_path_if (.csrng_cmd_i(csrng_cmd_i));
  csrng_assert_if csrng_assert_if (.csrng_cmd_i(csrng_cmd_i));

  `DV_ALERT_IF_CONNECT

  // dut
  csrng#(.NHwApps(NUM_HW_APPS),
         .RndCnstCsKeymgrDivNonProduction(LC_HW_DEBUG_EN_ON_DATA),
         .RndCnstCsKeymgrDivProduction(LC_HW_DEBUG_EN_OFF_DATA))
  dut (
    .clk_i                      (clk      ),
    .rst_ni                     (rst_n    ),

    .tl_i                       (tl_if.h2d),
    .tl_o                       (tl_if.d2h),

    .otp_en_csrng_sw_app_read_i (prim_mubi_pkg::mubi8_t'(otp_en_cs_sw_app_read)),

    .lc_hw_debug_en_i           (lc_ctrl_pkg::lc_tx_t'(lc_hw_debug_en)),

    .entropy_src_hw_if_o        (entropy_src_if.req),
    .entropy_src_hw_if_i        ({entropy_src_if.ack, entropy_src_if.d_data[entropy_src_pkg::
                                  CSRNG_BUS_WIDTH-1:0], entropy_src_if.d_data[entropy_src_pkg::
                                  CSRNG_BUS_WIDTH]}),

    .cs_aes_halt_i              (aes_halt_if.req),
    .cs_aes_halt_o              (aes_halt_if.ack),

    .csrng_cmd_i                (csrng_cmd_req),
    .csrng_cmd_o                (csrng_cmd_rsp),

    .alert_rx_i                 (alert_rx),
    .alert_tx_o                 (alert_tx),

    .intr_cs_cmd_req_done_o     (intr_cmd_req_done),
    .intr_cs_entropy_req_o      (intr_entropy_req),
    .intr_cs_hw_inst_exc_o      (intr_hw_inst_exc),
    .intr_cs_fatal_err_o        (intr_cs_fatal_err)
  );

  for (genvar i = 0; i < NUM_HW_APPS; i++) begin : gen_csrng_if
    assign csrng_cmd_req[i]    = csrng_if[i].cmd_req;
    assign csrng_if[i].cmd_rsp = csrng_cmd_rsp[i];
    initial begin
      uvm_config_db#(virtual csrng_if)::set(null, $sformatf("*.env.m_edn_agent[%0d]*", i),
          "vif", csrng_if[i]);
    end
  end

  assign interrupts[CmdReqDone] = intr_cmd_req_done;
  assign interrupts[EntropyReq] = intr_entropy_req;
  assign interrupts[HwInstExc]  = intr_hw_inst_exc;
  assign interrupts[FifoErr]    = intr_cs_fatal_err;
  // No data
  assign aes_halt_if.d_data = '0;

  initial begin
    // Drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual pins_if#(MuBi8Width))::set(null, "*.env", "otp_en_cs_sw_app_read_vif",
        otp_en_cs_sw_app_read_if);
    uvm_config_db#(virtual pins_if#(MuBi4Width))::set(null, "*.env", "lc_hw_debug_en_vif",
        lc_hw_debug_en_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual push_pull_if#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)))::
      set(null, "*.env.m_entropy_src_agent*", "vif", entropy_src_if);
    uvm_config_db#(virtual push_pull_if#(.HostDataWidth(1)))::set
        (null, "*.env.m_aes_halt_agent*", "vif", aes_halt_if);
    uvm_config_db#(virtual csrng_cov_if)::set(null, "*.env", "csrng_cov_if", dut.u_csrng_cov_if);
    uvm_config_db#(virtual csrng_assert_if)::set(null, "*.env", "csrng_assert_vif",
                                                 csrng_assert_if);
    uvm_config_db#(virtual csrng_path_if)::set(null, "*.env", "csrng_path_vif", csrng_path_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  // Assertions
  for (genvar i = 0; i < NUM_HW_APPS + 1; i++) begin : gen_cmd_stage_asserts
    `ASSERT(CmdStageFifoNotFullReady,
      (tb.dut.u_csrng_core.gen_cmd_stage[i].u_csrng_cmd_stage.sfifo_cmd_depth != 2'h2) |->
      tb.dut.u_csrng_core.gen_cmd_stage[i].u_csrng_cmd_stage.cmd_stage_rdy_o,
      clk,
      !rst_n)
    `ASSERT(CmdStageFifoFullNotReady,
      (tb.dut.u_csrng_core.gen_cmd_stage[i].u_csrng_cmd_stage.sfifo_cmd_depth == 2'h2) |->
      !tb.dut.u_csrng_core.gen_cmd_stage[i].u_csrng_cmd_stage.cmd_stage_rdy_o,
      clk,
      !rst_n)
    `DV_ASSERT_CTRL("CmdStageFifoAsserts", CmdStageFifoNotFullReady)
    `DV_ASSERT_CTRL("CmdStageFifoAsserts", CmdStageFifoFullNotReady)
  end

endmodule
