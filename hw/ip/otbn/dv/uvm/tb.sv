// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages (test)
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import mem_bkdr_util_pkg::mem_bkdr_util;
  import otbn_env_pkg::*;
  import otbn_test_pkg::*;
  import otbn_pkg::NGpr, otbn_pkg::NWdr;

  // dep packages (rtl)
  import otbn_reg_pkg::*;
  import edn_pkg::*;
  import otp_ctrl_pkg::*;
  import keymgr_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire intr_done;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if                    clk_rst_if  (.clk(clk), .rst_n(rst_n));
  tl_if                         tl_if       (.clk(clk), .rst_n(rst_n));
  otbn_escalate_if              escalate_if (.clk_i (clk), .rst_ni (rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if     (interrupts);
  assign interrupts[0] = {intr_done};

  otbn_key_req_t sideload_key;
  key_sideload_if#(keymgr_pkg::otbn_key_req_t) keymgr_if (
    .clk_i        (clk),
    .rst_ni       (rst_n),
    .sideload_key (sideload_key)
  );

  otbn_model_if #(
    .ImemSizeByte (ImemSizeByte)
  ) model_if (
    .clk_i         (clk),
    .rst_ni        (rst_n),
    .keymgr_key_i  (sideload_key)
  );

  // OTP Interface related connections
  localparam logic [127:0] TestScrambleKey = 128'h48ecf6c738f0f108a5b08620695ffd4d;
  localparam logic [63:0]  TestScrambleNonce = 64'hf88c2578fa4cd123;

  otbn_otp_key_req_t otp_key_req;
  otbn_otp_key_rsp_t otp_key_rsp;

  otp_ctrl_pkg::otbn_key_t   key;
  otp_ctrl_pkg::otbn_nonce_t nonce;
  wire seed_valid;

  wire otp_rst_n = rst_n;
  wire otp_clk;

  clk_rst_if otp_clk_rst_if(.clk(otp_clk), .rst_n(otp_rst_n));

  // Initiate push pull interface for the OTP<->OTBN connections
  push_pull_if #(
    .DeviceDataWidth(KEY_RSP_DATA_SIZE)
  ) otp_key_if (
    .clk(otp_clk),
    .rst_n(otp_rst_n)
  );

  // OTP Key interface assignments
  assign otp_key_if.req         = otp_key_req.req;
  assign otp_key_rsp.ack        = otp_key_if.ack;
  assign otp_key_rsp.key        = key;
  assign otp_key_rsp.nonce      = nonce;
  assign otp_key_rsp.seed_valid = seed_valid;
  // key, nonce, seed_valid all driven by push_pull Device interface
  assign {key, nonce, seed_valid} = otp_key_if.d_data;

  // edn_clk, edn_rst_n and edn_if is defined and driven in below macro
  `DV_EDN_IF_CONNECT

  `DV_ALERT_IF_CONNECT()

  // dut
  otbn # (
    .RndCnstOtbnKey(TestScrambleKey),
    .RndCnstOtbnNonce(TestScrambleNonce)
  ) dut (
    .clk_i (clk),
    .rst_ni(rst_n),

    .tl_i(tl_if.h2d),
    .tl_o(tl_if.d2h),

    // Correct behaviour of the idle output is ensured by the bound-in otbn_idle_checker instance.
    .idle_o(),

    .intr_done_o(intr_done),

    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx),

    .lc_escalate_en_i(escalate_if.enable),
    .lc_rma_req_i    (escalate_if.req),
    .lc_rma_ack_o    (escalate_if.ack),

    .ram_cfg_i('0),

    .clk_edn_i (edn_clk),
    .rst_edn_ni(edn_rst_n),

    .edn_rnd_o (edn_if[RndEdnIdx].req),
    .edn_rnd_i ({edn_if[RndEdnIdx].ack, edn_if[RndEdnIdx].d_data}),

    .edn_urnd_o(edn_if[UrndEdnIdx].req),
    .edn_urnd_i({edn_if[UrndEdnIdx].ack, edn_if[UrndEdnIdx].d_data}),

    .clk_otp_i     (otp_clk),
    .rst_otp_ni    (otp_rst_n),
    .otbn_otp_key_o(otp_key_req),
    .otbn_otp_key_i(otp_key_rsp),

    .keymgr_key_i(sideload_key)
  );

  bind dut.u_otbn_core otbn_trace_if #(
    .ImemAddrWidth (ImemAddrWidth),
    .DmemAddrWidth (DmemAddrWidth)
  ) i_otbn_trace_if (.*);

  assign dut.u_otbn_core.i_otbn_trace_if.scramble_state_err_i = dut.otbn_scramble_state_error;
  assign dut.u_otbn_core.i_otbn_trace_if.missed_gnt_i.imem_gnt_missed_err = dut.imem_missed_gnt;
  assign dut.u_otbn_core.i_otbn_trace_if.missed_gnt_i.dmem_gnt_missed_err = dut.dmem_missed_gnt;

  bind dut.u_otbn_core otbn_tracer u_otbn_tracer(.*, .otbn_trace(i_otbn_trace_if));

  bind dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller
    otbn_loop_if i_otbn_loop_if (
      .clk_i,
      .rst_ni,
      // The insn_addr_i signal in the loop controller is of width ImemAddrWidth. We expand it to a
      // 32-bit address here to avoid having to parameterise the type of the interface.
      .insn_addr_i (32'(insn_addr_i)),
      .at_current_loop_end_insn,
      .current_loop_valid,
      .loop_stack_full,
      .current_loop_finish,
      .next_loop_valid,
      .loop_start_req_i,
      .loop_start_commit_i,
      .loop_iterations_i,
      .otbn_stall_i,

      // These addresses are start/end addresses for entries in the loop stack. As with insn_addr_i,
      // we expand them to 32 bits. Also the loop stack entries have a type that's not exposed
      // outside of the loop controller module so we need to extract the fields here.
      .current_loop_start (32'(current_loop.loop_addr_info.loop_start)),
      .current_loop_end   (32'(current_loop.loop_addr_info.loop_end)),
      .next_loop_end      (32'(prefetch_loop_end_addr_o)),

      // These counts are used by the loop warping code.
      .current_loop_d_iterations (prefetch_loop_iterations_o),
      .current_loop_q_iterations (current_loop.loop_iterations),

      .loop_stack_rd_idx,
      .loop_stack_push,
      .loop_stack_pop
    );

  bind dut.u_otbn_core.u_otbn_alu_bignum otbn_alu_bignum_if i_otbn_alu_bignum_if (.*);
  bind dut.u_otbn_core.u_otbn_controller otbn_controller_if i_otbn_controller_if (.*);
  bind dut.u_otbn_core.u_otbn_mac_bignum otbn_mac_bignum_if i_otbn_mac_bignum_if (.*);
  bind dut.u_otbn_core.u_otbn_rf_base otbn_rf_base_if i_otbn_rf_base_if (.*);

  bind dut.u_otbn_core.u_otbn_rnd otbn_rnd_if i_otbn_rnd_if (.*);

  // OTBN model, wrapping an ISS.
  //
  // Note that we pull the "start" signal out of the DUT. This is because it's much more difficult
  // to grab the decoded signal from TL transactions on the cycle it happens. We have an explicit
  // check in the scoreboard to ensure that this gets asserted at the time we expect (to spot any
  // decoding errors).
  assign model_if.cmd_q = dut.reg2hw.cmd.q;
  assign model_if.cmd_qe = dut.reg2hw.cmd.qe;

  // Valid signals below are set when DUT finishes processing incoming 32b packages and constructs
  // 256b EDN data. Model checks if the processing of the packages are done in maximum of 5 cycles
  logic edn_rnd_cdc_done, edn_rnd_req_model;
  logic edn_urnd_cdc_done, edn_urnd_req_model;
  logic otp_key_cdc_done;

  assign edn_rnd_cdc_done = dut.edn_rnd_req & dut.edn_rnd_ack;
  assign edn_urnd_cdc_done = dut.edn_urnd_req & dut.edn_urnd_ack;
  assign otp_key_cdc_done = dut.u_otbn_scramble_ctrl.otp_key_ack;

  bit [31:0] model_insn_cnt;

  otbn_core_model #(
    .MemScope     ("..dut"),
    .DesignScope  ("..dut.u_otbn_core")
  ) u_model (
    .clk_i     (model_if.clk_i),
    .clk_edn_i (edn_clk),
    .rst_ni    (model_if.rst_ni),
    .rst_edn_ni(edn_rst_n),

    .cmd_i   (model_if.cmd_q),
    .cmd_en_i(model_if.cmd_qe),

    .lc_escalate_en_i(escalate_if.enable),
    .lc_rma_req_i    (escalate_if.req),

    .err_bits_o(model_if.err_bits),

    .edn_rnd_i         ({edn_if[RndEdnIdx].ack, edn_if[RndEdnIdx].d_data}),
    .edn_rnd_o         (edn_rnd_req_model),
    .edn_rnd_cdc_done_i(edn_rnd_cdc_done),

    .edn_urnd_i         ({edn_if[UrndEdnIdx].ack, edn_if[UrndEdnIdx].d_data}),
    .edn_urnd_o         (edn_urnd_req_model),
    .edn_urnd_cdc_done_i(edn_urnd_cdc_done),

    .init_sec_wipe_done_i(dut.u_otbn_core.i_otbn_trace_if.initial_secure_wipe_done),

    .otp_key_cdc_done_i(otp_key_cdc_done),

    .status_o  (model_if.status),
    .insn_cnt_o(model_insn_cnt),

    .done_rr_o(),

    .err_o(model_if.err),

    .keymgr_key_i(model_if.keymgr_key_i)
  );

  // Pull the final PC and the OtbnModel handle out of the SV model wrapper.
  assign model_if.stop_pc = u_model.stop_pc_q;
  // The always_ff is because the spec doesn't allow continuous assignments for chandles. The value
  // is populated in an init block and we'll only read this when the start signal is asserted, which
  // will be much more than 1 cycle later, so we shouldn't need to worry about a stale value.
  always_ff @(posedge model_if.clk_i) begin
    model_if.handle <= u_model.model_handle;
  end

  otbn_insn_cnt_if insn_cnt_if (
   .clk_i            (clk),
   .rst_ni           (rst_n),

   .insn_cnt_i       (dut.insn_cnt),
   .insn_executing_i (dut.u_otbn_core.u_otbn_controller.insn_executing),
   .stall_i          (dut.u_otbn_core.u_otbn_controller.stall),

   .model_insn_cnt_i (model_insn_cnt)
  );

  //////////////////////////////////////////////////////////////////////////////
  // Model/RTL consistency checks
  //
  // These are the sort of checks that are easier to state at the design level than in terms of UVM
  // transactions.

  // Check that the status output from the model exactly matches the register from the dut. In
  // theory, we could see mismatches by probing the STATUS register over the TL bus, but we have to
  // be lucky with exactly when the reads happen if we want to see off-by-one cycle errors. This
  // assertion gives a continuous check.
  `ASSERT(MatchingStatus_A, dut.u_reg.u_status.q == model_if.status, clk, !rst_n)

  // Check that if the modelled EDN requests are matching with the requests from DUT
  `ASSERT(MatchingReqRND_A, dut.u_otbn_core.edn_rnd_req_o == edn_rnd_req_model, clk, !rst_n)
  // Disable checking URND in the case of Locked status since it's modelling is not exactly accurate
  // for that state.
  // TODO (#15710): Fix modelling of URND in the locked state.
  `ASSERT(MatchingReqURND_A, dut.u_otbn_core.edn_urnd_req_o == edn_urnd_req_model,
    clk, !rst_n || model_if.status == otbn_pkg::StatusLocked)

  initial begin
    mem_bkdr_util imem_util, dmem_util;

    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    otp_clk_rst_if.set_active(.drive_rst_n_val(1'b0));

    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "otp_clk_rst_vif", otp_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(escalate_vif)::set(null, "*.env", "escalate_vif", escalate_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual otbn_model_if)::set(null, "*.env.model_agent", "vif", model_if);
    uvm_config_db#(virtual key_sideload_if#(keymgr_pkg::otbn_key_req_t))::set(
      null, "*.env.keymgr_sideload_agent", "vif", keymgr_if);

    uvm_config_db#(otp_key_vif)::set(
      null, "*.env.key_agent*", "vif", otp_key_if);

    uvm_config_db#(virtual otbn_trace_if)::set(null, "*.env", "trace_vif",
                                               dut.u_otbn_core.i_otbn_trace_if);
    uvm_config_db#(virtual otbn_loop_if)::set(
      null, "*.env", "loop_vif",
      dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller.i_otbn_loop_if);
    uvm_config_db#(virtual otbn_alu_bignum_if)::set(
      null, "*.env", "alu_bignum_vif",
      dut.u_otbn_core.u_otbn_alu_bignum.i_otbn_alu_bignum_if);
    uvm_config_db#(virtual otbn_controller_if)::set(
      null, "*.env", "controller_vif",
      dut.u_otbn_core.u_otbn_controller.i_otbn_controller_if);
    uvm_config_db#(virtual otbn_mac_bignum_if)::set(
      null, "*.env", "mac_bignum_vif",
      dut.u_otbn_core.u_otbn_mac_bignum.i_otbn_mac_bignum_if);
    uvm_config_db#(virtual otbn_rf_base_if)::set(
      null, "*.env", "rf_base_vif",
      dut.u_otbn_core.u_otbn_rf_base.i_otbn_rf_base_if);
    uvm_config_db#(virtual otbn_rnd_if)::set(
      null, "*.env", "rnd_vif",
      dut.u_otbn_core.u_otbn_rnd.i_otbn_rnd_if);

    // Instantiate mem_bkdr_util objects to allow access to IMEM and DMEM
    //
    // Note that n_bits is the number of bits in the memory, including ECC check bits.
    imem_util = new(.name ("imem_util"),
                    .path ({"tb.dut.u_imem.u_prim_ram_1p_adv.",
                            "u_mem.gen_generic.u_impl_generic.mem"}),
                    .depth (ImemSizeByte / 4),
                    .n_bits (ImemSizeByte / 4 * 39),
                    .err_detection_scheme (mem_bkdr_util_pkg::EccInv_39_32));

    // DMEM is twice as big as the bus-accessible part
    dmem_util = new(.name ("dmem_util"),
                    .path ({"tb.dut.u_dmem.u_prim_ram_1p_adv.",
                            "u_mem.gen_generic.u_impl_generic.mem"}),
                    .depth (DmemSizeByte / 32),
                    .n_bits (DmemSizeByte / 32 * 312),
                    .err_detection_scheme (mem_bkdr_util_pkg::EccInv_39_32));

    uvm_config_db#(mem_bkdr_util)::set(null, "*.env", imem_util.get_name(), imem_util);
    uvm_config_db#(mem_bkdr_util)::set(null, "*.env", dmem_util.get_name(), dmem_util);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  // Assertion controls for turning them on/off easily

  // A hook to allow sequences to enable or disable the MatchingStatus_A assertion below. This is
  // needed for sequences that trigger alerts (locking OTBN) without telling the model.
  `DV_ASSERT_CTRL("otbn_status_assert_en", tb.MatchingStatus_A)

  // We need to turn off DMEM related assertions in the tests where we force internals of DMEM to generate errors
  `DV_ASSERT_CTRL("DMemAsserts", tb.dut.u_otbn_core.u_otbn_lsu.DMemRValidAfterReq)
  `DV_ASSERT_CTRL("DMemAsserts", tb.dut.u_otbn_core.OnlyWriteLoadDataBaseWhenDMemValid_A)
  `DV_ASSERT_CTRL("DMemAsserts", tb.dut.u_otbn_core.OnlyWriteLoadDataBignumWhenDMemValid_A)

endmodule
