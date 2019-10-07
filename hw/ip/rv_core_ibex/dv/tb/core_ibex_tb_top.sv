// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module core_ibex_tb_top;

  import uvm_pkg::*;

  `include "tl_if_connect_macros.svh"

  logic clk;
  logic rst_n;
  logic fetch_enable;

  clk_if ibex_clk_if(.clk(clk));

  // TODO Resolve the tied-off ports
  // The interrupt and debug interface ports might be changed to RISC-V compliant interface, these
  // interfaces will be connected after design is ready.
  rv_core_ibex dut(
    .clk_i(clk),
    .rst_ni(rst_n),
    .test_en_i(1'b1),
    .hart_id_i(32'b0),
    .boot_addr_i(`BOOT_ADDR), // align with spike boot address
    .irq_i('0),
    .irq_id_i('0),
    .debug_req_i('0),
    .fetch_enable_i(fetch_enable)
  );

  `CONNECT_TL_DEVICE_IF(instr_tl_if, dut.tl_i_o, dut.tl_i_i, instr)
  `CONNECT_TL_DEVICE_IF(data_tl_if, dut.tl_d_o, dut.tl_d_i, data)

  // DUT probe interface
  core_ibex_dut_probe_if dut_if(.clk(clk));
  assign dut_if.ecall = dut.u_core.id_stage_i.ecall_insn_dec;
  assign fetch_enable = dut_if.fetch_enable;

  initial begin
    uvm_config_db#(virtual clk_if)::set(null, "*", "clk_if", ibex_clk_if);
    uvm_config_db#(virtual core_ibex_dut_probe_if)::set(null, "*", "dut_if", dut_if);
    run_test();
  end

  // Generate clk
  initial begin
    clk = 1'b0;
    forever begin
      #10 clk = ~clk;
    end
  end

  // Generate reset
  initial begin
    rst_n = 1'b0;
    repeat(100) @(posedge clk);
    rst_n = 1'b1;
  end

endmodule
