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

  // dut
  otbn dut (
    .clk_i       (clk),
    .rst_ni      (rst_n),

    .tl_i        (tl_if.h2d),
    .tl_o        (tl_if.d2h),

    .idle_o      (idle),

    .intr_done_o (intr_done),

    .alert_rx_i  (alert_rx),
    .alert_tx_o  (alert_tx)

  );

  bind otbn_core otbn_trace_if #(
    .ImemAddrWidth (ImemAddrWidth),
    .DmemAddrWidth (DmemAddrWidth)
  ) i_otbn_trace_if (.*);

  bind otbn_core otbn_tracer u_otbn_tracer(.*, .otbn_trace(i_otbn_trace_if));

  // OTBN model, wrapping an ISS.
  //
  // Note that we pull the "start" signal out of the DUT. This is because it's much more difficult
  // to grab the decoded signal from TL transactions on the cycle it happens. We have an explicit
  // check in the scoreboard to ensure that this gets asserted at the time we expect (to spot any
  // decoding errors).
  assign model_if.start = dut.start;

  localparam ImemScope = "..dut.u_imem.u_mem.gen_generic.u_impl_generic";
  localparam DmemScope = "..dut.u_dmem.u_mem.gen_generic.u_impl_generic";
  localparam DesignScope = "..dut.u_otbn_core";

  otbn_core_model #(
    .DmemSizeByte (otbn_reg_pkg::OTBN_DMEM_SIZE),
    .ImemSizeByte (otbn_reg_pkg::OTBN_IMEM_SIZE),
    .DmemScope    (DmemScope),
    .ImemScope    (ImemScope),
    .DesignScope  (DesignScope)
  ) u_model (
    .clk_i        (model_if.clk_i),
    .rst_ni       (model_if.rst_ni),

    .start_i      (model_if.start),
    .done_o       (model_if.done),
    .start_addr_i (model_if.start_addr),
    .err_o        (model_if.err)
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();

    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(idle_vif)::set(null, "*.env", "idle_vif", idle_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual otbn_model_if)::set(null, "*.env.model_agent", "vif", model_if);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
