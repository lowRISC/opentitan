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

  // Mock up EDN that just instantly returns fixed data when requested
  // TODO: Provide a proper EDN agent
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

  // dut
  otbn dut (
    .clk_i       (clk),
    .rst_ni      (rst_n),

    .tl_i        (tl_if.h2d),
    .tl_o        (tl_if.d2h),

    .idle_o      (idle),

    .intr_done_o (intr_done),

    .alert_rx_i  (alert_rx),
    .alert_tx_o  (alert_tx),

    .clk_edn_i  (clk),
    .rst_edn_ni (rst_n),
    .edn_rnd_o ( edn_rnd_req ),
    .edn_rnd_i ( edn_rnd_rsp ),

    .edn_urnd_o ( edn_urnd_req ),
    .edn_urnd_i ( edn_urnd_rsp )
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
      // As with insn_addr_i, we expand this to 32 bits. Also, current_loop_q has a type that's not
      // exposed outside of the loop controller module so we need to extract the loop_end field
      // here.
      .current_loop_end (32'(current_loop_q.loop_end))
    );

  bind dut.u_otbn_core.u_otbn_alu_bignum otbn_alu_bignum_if i_otbn_alu_bignum_if (.*);
  bind dut.u_otbn_core.u_otbn_mac_bignum otbn_mac_bignum_if i_otbn_mac_bignum_if (.*);

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
    .start_addr_i (model_if.start_addr),
    .err_o        (model_if.err),

    .edn_rnd_data_valid_i  (edn_rnd_data_valid),
    .edn_rnd_data_i        (dut.edn_rnd_data),
    .edn_urnd_data_valid_i (edn_urnd_data_valid)
  );

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

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
