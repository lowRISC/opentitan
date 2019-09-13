// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Sample testbench for Ibex with tracing enabled
// The `nop` instruction is the only input

module ibex_tracing_tb;
  logic         clk          = 1'b0;
  logic         rst_n        = 1'b0;
  logic [31:0]  instr_rdata  = 32'h00000013;
  logic [31:0]  data_rdata   = 32'h00000000;
  logic         instr_gnt    = 1'b0;
  logic         instr_rvalid = 1'b0;

  initial begin: clock_gen
    forever begin
      #5ns clk = 1'b0;
      #5ns clk = 1'b1;
    end
  end

  initial begin: reset_gen
    rst_n = 1'b0;
    #160ns rst_n = 1'b1;
    #400ns $finish;
  end

  initial begin: instr_gen
    #200ns instr_rdata  = 32'h81868106;
           instr_rvalid = 1'b0;
           instr_gnt    = 1'b1;
    #10ns  instr_rvalid = 1'b1;
           instr_gnt    = 1'b0;
    #10ns  instr_rvalid = 1'b0;
    #30ns  instr_rdata  = 32'h00400113;
           instr_rvalid = 1'b0;
           instr_gnt    = 1'b1;
    #10ns  instr_rvalid = 1'b1;
           instr_gnt    = 1'b0;
    #10ns  instr_rvalid = 1'b0;
           instr_rdata  = 32'hff810113;
           instr_gnt    = 1'b1;
    #10ns  instr_rvalid = 1'b1;
           instr_gnt    = 1'b0;
    #10ns  instr_rvalid = 1'b0;
           instr_rdata  = 32'h4000006f;
           instr_gnt    = 1'b1;
    #10ns  instr_rvalid = 1'b1;
           instr_gnt    = 1'b0;
    #10ns  instr_rvalid = 1'b0;
    #10ns  instr_rdata  = 32'h039597b3;
           instr_gnt    = 1'b1;
    #10ns  instr_rvalid = 1'b1;
           instr_gnt    = 1'b1;
    #10ns  instr_rdata  = 32'h13410d13;
    #10ns  instr_rdata  = 32'he1070713;
    #10ns  instr_rdata  = 32'hfff7c793;
    #10ns  instr_rdata  = 32'h00000013;
    #10ns  instr_rdata  = 32'h002d2c23;
    #10ns  instr_rdata  = 32'h00000013;
    #10ns  instr_rdata  = 32'h000d2083;
           data_rdata   = 32'h12345678;
    #10ns  instr_rdata  = 32'h60008113;
    #10ns  instr_rdata  = 32'h00000013;
    #10ns  instr_rdata  = 32'h002d2023;
    #20ns  instr_rdata  = 32'h0000000f;
    #10ns  instr_rdata  = 32'h00000113;
    #30ns  instr_rdata  = 32'h00000013;
    #10ns  instr_rdata  = 32'h0000000f;
  end

  ibex_core_tracing ibex_i (
    .clk_i                  (clk),
    .rst_ni                 (rst_n),

    .test_en_i              (1'b0),

    // Core ID, Cluster ID and boot address are considered more or less static
    .hart_id_i              (32'b0),
    .boot_addr_i            (32'b0),

    // Instruction memory interface
    .instr_req_o            (),
    .instr_gnt_i            (instr_gnt),
    .instr_rvalid_i         (instr_rvalid),
    .instr_addr_o           (),
    .instr_rdata_i          (instr_rdata),
    .instr_err_i            (1'b0),

    // Data memory interface
    .data_req_o             (),
    .data_gnt_i             (1'b1),
    .data_rvalid_i          (1'b1),
    .data_we_o              (),
    .data_be_o              (),
    .data_addr_o            (),
    .data_wdata_o           (),
    .data_rdata_i           (data_rdata),
    .data_err_i             (1'b0),

    // Interrupt inputs
    .irq_software_i         (1'b0),
    .irq_timer_i            (1'b0),
    .irq_external_i         (1'b0),
    .irq_fast_i             (15'b0),
    .irq_nm_i               (1'b0),

    // Debug Interface
    .debug_req_i            (1'b0),

    // CPU Control Signals
    .fetch_enable_i         (1'b1),
    .core_sleep_o           ()
  );

endmodule
