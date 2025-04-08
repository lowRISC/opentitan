// Copyright lowRISC contributors (OpenTitan project).
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

  wire   clk, rst_n;
  wire   edn_disable, entropy_src_disable;
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
  pins_if#(MuBi8Width) otp_en_cs_sw_app_read_if(otp_en_cs_sw_app_read);
  pins_if#(MuBi4Width) lc_hw_debug_en_if(lc_hw_debug_en);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  csrng_if  csrng_if[NUM_HW_APPS](.clk(clk), .rst_n(edn_disable === 1'b1 ? 1'b0 : rst_n));
  csrng_agents_if csrng_agents_if();
  push_pull_if#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))
      entropy_src_if(.clk(clk), .rst_n(entropy_src_disable === 1'b1 ? 1'b0 : rst_n));
  push_pull_if#(.HostDataWidth(1))   aes_halt_if(.clk(clk), .rst_n(rst_n));
  csrng_path_if csrng_path_if (.csrng_cmd_i(csrng_cmd_i));

  bind dut csrng_assert_if csrng_assert_if (.csrng_cmd_i(csrng_cmd_i));

  // All CSRNG-EDN interfaces (and therefore EDN agents) can currently only be disabled together.
  assign edn_disable = csrng_agents_if.edn_disable;
  assign entropy_src_disable = csrng_agents_if.entropy_src_disable;

  `DV_ALERT_IF_CONNECT()

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
                                                 dut.csrng_assert_if);
    uvm_config_db#(virtual csrng_path_if)::set(null, "*.env", "csrng_path_vif", csrng_path_if);
    uvm_config_db#(virtual csrng_agents_if)::set(null, "*.env", "csrng_agents_vif",
                                                 csrng_agents_if);
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

  // Ensure that upon local escalation of the AES cipher core inside Block Encrypt, no intermediate
  // v is released into the ctr_drbg_gen/update blocks.
  `define BLOCK_ENCRYPT_PATH tb.dut.u_csrng_core.u_csrng_block_encrypt
  `define CTR_DRBG_GEN tb.dut.u_csrng_core.u_csrng_ctr_drbg_gen
  `define CTR_DRBG_GEN_FIFO `CTR_DRBG_GEN.u_prim_fifo_sync_bencack.gen_singleton_fifo
  `ASSERT_INIT(CsrngCtrDrbgGenFifoDepth1, `CTR_DRBG_GEN.BlkEncAckFifoDepth == 1)
  `ASSERT(CsrngSecCmAesCipherDataRegLocalEscGen,
      $rose(`CTR_DRBG_GEN_FIFO.full_q) &&
      `BLOCK_ENCRYPT_PATH.block_encrypt_aes_cipher_sm_err_o |=>
      $past(`CTR_DRBG_GEN_FIFO.storage
          [`CTR_DRBG_GEN.BlkEncAckFifoWidth-1 -: `CTR_DRBG_GEN.BlkLen]) !=
      $past(`BLOCK_ENCRYPT_PATH.cipher_data_out, 2), clk, !rst_n)

  `define CTR_DRBG_UPD tb.dut.u_csrng_core.u_csrng_ctr_drbg_upd
  `define CTR_DRBG_UPD_FIFO `CTR_DRBG_UPD.u_prim_fifo_sync_bencack.gen_singleton_fifo
  `ASSERT_INIT(CsrngCtrDrbgUpdFifoDepth1, `CTR_DRBG_UPD.BlkEncAckFifoDepth == 1)
  `ASSERT(CsrngSecCmAesCipherDataRegLocalEscUpd,
      $rose(`CTR_DRBG_UPD_FIFO.full_q) &&
      `BLOCK_ENCRYPT_PATH.block_encrypt_aes_cipher_sm_err_o |=>
      $past(`CTR_DRBG_UPD_FIFO.storage
          [`CTR_DRBG_UPD.BlkEncAckFifoWidth-1 -: `CTR_DRBG_UPD.BlkLen]) !=
      $past(`BLOCK_ENCRYPT_PATH.cipher_data_out, 2), clk, !rst_n)

  // Assertion controls
  `DV_ASSERT_CTRL("EntropySrcIf_ReqHighUntilAck_A_CTRL", entropy_src_if.ReqHighUntilAck_A)
  `DV_ASSERT_CTRL("EntropySrcIf_AckAssertedOnlyWhenReqAsserted_A_CTRL",
                  entropy_src_if.AckAssertedOnlyWhenReqAsserted_A)

endmodule
