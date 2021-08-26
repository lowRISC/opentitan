// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages (test)
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import otbn_env_pkg::*;
  import otbn_test_pkg::*;

  // dep packages (rtl)
  import otbn_reg_pkg::*;
  import edn_pkg::*;
  import otp_ctrl_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire idle, intr_done;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if                    clk_rst_if (.clk(clk), .rst_n(rst_n));
  tl_if                         tl_if      (.clk(clk), .rst_n(rst_n));
  pins_if #(1)                  idle_if    (idle);
  pins_if #(NUM_MAX_INTERRUPTS) intr_if    (interrupts);
  assign interrupts[0] = {intr_done};

  otbn_model_if #(
    .ImemSizeByte (otbn_reg_pkg::OTBN_IMEM_SIZE)
  ) model_if (
    .clk_i  (clk),
    .rst_ni (rst_n)
  );

  `DV_ALERT_IF_CONNECT

  // Mock up EDN & OTP that just instantly return fixed data when requested
  // TODO: Provide proper EDN and OTP agents
  edn_req_t edn_rnd_req;
  edn_rsp_t edn_rnd_rsp;

  edn_req_t edn_urnd_req;
  edn_rsp_t edn_urnd_rsp;

  assign edn_rnd_rsp.edn_ack  = edn_rnd_req.edn_req;
  assign edn_rnd_rsp.edn_fips = 1'b0;
  assign edn_rnd_rsp.edn_bus  = 32'h99999999;

  assign edn_urnd_rsp.edn_ack  = edn_urnd_req.edn_req;
  assign edn_urnd_rsp.edn_fips = 1'b0;
  assign edn_urnd_rsp.edn_bus  = 32'h99999999;

  otbn_otp_key_req_t otp_key_req;
  otbn_otp_key_rsp_t otp_key_rsp;

  logic otp_key_ack_q;

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      otp_key_ack_q <= 1'b0;
    end else begin
      otp_key_ack_q <= otp_key_req.req;
    end
  end

  localparam logic [127:0] TestScrambleKey = 128'h48ecf6c738f0f108a5b08620695ffd4d;
  localparam logic [63:0]  TestScrambleNonce = 64'hf88c2578fa4cd123;

  assign otp_key_rsp.ack = otp_key_ack_q;
  assign otp_key_rsp.key = TestScrambleKey;
  assign otp_key_rsp.nonce = TestScrambleNonce;
  assign otp_key_rsp.seed_valid = 1'b0;

  // dut
  otbn # (
    .RndCnstOtbnKey(TestScrambleKey),
    .RndCnstOtbnNonce(TestScrambleNonce)
  ) dut (
    .clk_i (clk),
    .rst_ni(rst_n),

    .tl_i(tl_if.h2d),
    .tl_o(tl_if.d2h),

    .idle_o(idle),
    // TODO: Once this signal's behaviour is specified, check that it behaves as we expect.
    .idle_otp_o (),

    .intr_done_o(intr_done),

    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx),

    .lc_escalate_en_i (lc_ctrl_pkg::Off),

    .ram_cfg_i('0),

    .clk_edn_i (clk),
    .rst_edn_ni(rst_n),
    .edn_rnd_o (edn_rnd_req),
    .edn_rnd_i (edn_rnd_rsp),

    .edn_urnd_o(edn_urnd_req),
    .edn_urnd_i(edn_urnd_rsp),

    .clk_otp_i     (clk),
    .rst_otp_ni    (rst_n),
    .otbn_otp_key_o(otp_key_req),
    .otbn_otp_key_i(otp_key_rsp)
  );

  bind dut.u_otbn_core otbn_trace_if #(
    .ImemAddrWidth (ImemAddrWidth),
    .DmemAddrWidth (DmemAddrWidth)
  ) i_otbn_trace_if (.*);

  bind dut.u_otbn_core otbn_tracer u_otbn_tracer(.*, .otbn_trace(i_otbn_trace_if));

  bind dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller
    otbn_loop_if i_otbn_loop_if (
      .clk_i,
      .rst_ni,
      // The insn_addr_i signal in the loop controller is of width ImemAddrWidth. We expand it to a
      // 32-bit address here to avoid having to parameterise the type of the interface.
      .insn_addr_i (32'(insn_addr_i)),
      .at_current_loop_end_insn,
      .loop_active_q,
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
      .current_loop_start (32'(current_loop_q.loop_start)),
      .current_loop_end   (32'(current_loop_q.loop_end)),
      .next_loop_end      (32'(next_loop.loop_end)),

      // This count is used by the loop warping code.
      .current_loop_d_iterations (current_loop_d.loop_iterations)
    );

  bind dut.u_otbn_core.u_otbn_alu_bignum otbn_alu_bignum_if i_otbn_alu_bignum_if (.*);
  bind dut.u_otbn_core.u_otbn_mac_bignum otbn_mac_bignum_if i_otbn_mac_bignum_if (.*);
  bind dut.u_otbn_core.u_otbn_rf_base otbn_rf_base_if i_otbn_rf_base_if (.*);

  // OTBN model, wrapping an ISS.
  //
  // Note that we pull the "start" signal out of the DUT. This is because it's much more difficult
  // to grab the decoded signal from TL transactions on the cycle it happens. We have an explicit
  // check in the scoreboard to ensure that this gets asserted at the time we expect (to spot any
  // decoding errors).
  assign model_if.start = dut.start_q;

  // Internally otbn_core uses a 256-bit width interface for EDN data. This maps to muliple EDN
  // requests at this level (via a packing FIFO internal to otbn). The model works with the internal
  // otbn_core interface so probe into it here to provide the relevant signals to the model.
  logic edn_rnd_data_valid;
  logic edn_urnd_data_valid;

  assign edn_rnd_data_valid = dut.edn_rnd_req & dut.edn_rnd_ack;
  assign edn_urnd_data_valid = dut.edn_urnd_req & dut.edn_urnd_ack;

  bit [31:0] model_insn_cnt;

  otbn_core_model #(
    .DmemSizeByte (otbn_reg_pkg::OTBN_DMEM_SIZE),
    .ImemSizeByte (otbn_reg_pkg::OTBN_IMEM_SIZE),
    .MemScope     ("..dut"),
    .DesignScope  ("..dut.u_otbn_core")
  ) u_model (
    .clk_i        (model_if.clk_i),
    .rst_ni       (model_if.rst_ni),

    .start_i      (model_if.start),
    .done_o       (model_if.done),

    .err_bits_o   (),

    .start_addr_i (model_if.start_addr),

    .edn_rnd_data_valid_i  (edn_rnd_data_valid),
    .edn_rnd_data_i        (dut.edn_rnd_data),
    .edn_urnd_data_valid_i (edn_urnd_data_valid),

    .insn_cnt_o   (model_insn_cnt),
    .err_o        (model_if.err)
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

  // Check that the idle output from the DUT is the inverse of the model's "done" signal.
  // Separately, the code in otbn_idle_checker.sv checks that the idle output from the DUT is also
  // the inverse of the "done" signal that we expect. Combining the two tells us that the RTL and
  // model agree about whether they are running or not.
  `ASSERT(MatchingDone_A, idle == !model_if.done, clk, rst_n)


  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();

    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(idle_vif)::set(null, "*.env", "idle_vif", idle_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual otbn_model_if)::set(null, "*.env.model_agent", "vif", model_if);

    uvm_config_db#(virtual otbn_trace_if)::set(null, "*.env", "trace_vif",
                                               dut.u_otbn_core.i_otbn_trace_if);
    uvm_config_db#(virtual otbn_loop_if)::set(
      null, "*.env", "loop_vif",
      dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller.i_otbn_loop_if);
    uvm_config_db#(virtual otbn_alu_bignum_if)::set(
      null, "*.env", "alu_bignum_vif",
      dut.u_otbn_core.u_otbn_alu_bignum.i_otbn_alu_bignum_if);
    uvm_config_db#(virtual otbn_mac_bignum_if)::set(
      null, "*.env", "mac_bignum_vif",
      dut.u_otbn_core.u_otbn_mac_bignum.i_otbn_mac_bignum_if);
    uvm_config_db#(virtual otbn_rf_base_if)::set(
      null, "*.env", "rf_base_vif",
      dut.u_otbn_core.u_otbn_rf_base.i_otbn_rf_base_if);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
