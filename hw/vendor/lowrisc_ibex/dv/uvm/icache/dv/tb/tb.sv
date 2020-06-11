// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import ibex_icache_env_pkg::*;
  import ibex_icache_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));

  ibex_icache_core_if core_if (.clk(clk), .rst_n(rst_n));
  ibex_icache_mem_if  mem_if  (.clk(clk), .rst_n(rst_n));

  // dut
  ibex_icache dut (
    .clk_i           (clk),
    .rst_ni          (rst_n),

    // Connect icache <-> core interface
    .req_i           (core_if.req),
    .branch_i        (core_if.branch),
    .branch_spec_i   (core_if.branch_spec),
    .addr_i          (core_if.branch_addr),
    .ready_i         (core_if.ready),
    .valid_o         (core_if.valid),
    .rdata_o         (core_if.rdata),
    .addr_o          (core_if.addr),
    .err_o           (core_if.err),
    .err_plus2_o     (core_if.err_plus2),
    .icache_enable_i (core_if.enable),
    .icache_inval_i  (core_if.invalidate),
    .busy_o          (core_if.busy),

    // Connect icache <-> instruction bus interface
    .instr_req_o     (mem_if.req),
    .instr_gnt_i     (mem_if.gnt),
    .instr_addr_o    (mem_if.addr),
    .instr_rdata_i   (mem_if.rdata),
    .instr_err_i     (mem_if.err),
    .instr_pmp_err_i (mem_if.pmp_err),
    .instr_rvalid_i  (mem_if.rvalid)
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual ibex_icache_core_if)::set(null, "*.env.core_agent*", "vif", core_if);
    uvm_config_db#(virtual ibex_icache_mem_if)::set(null, "*.env.mem_agent*", "vif", mem_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
