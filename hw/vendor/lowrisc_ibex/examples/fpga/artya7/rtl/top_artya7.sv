// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_artya7 (
    input               IO_CLK,
    input               IO_RST_N,
    output [3:0]        LED
);

  parameter int          MEM_SIZE     = 64 * 1024; // 64 kB
  parameter logic [31:0] MEM_START    = 32'h00000000;
  parameter logic [31:0] MEM_MASK     = MEM_SIZE-1;
  parameter              SRAMInitFile = "";

  logic clk_sys, rst_sys_n;

  // Instruction connection to SRAM
  logic        instr_req;
  logic        instr_gnt;
  logic        instr_rvalid;
  logic [31:0] instr_addr;
  logic [31:0] instr_rdata;

  // Data connection to SRAM
  logic        data_req;
  logic        data_gnt;
  logic        data_rvalid;
  logic        data_we;
  logic  [3:0] data_be;
  logic [31:0] data_addr;
  logic [31:0] data_wdata;
  logic [31:0] data_rdata;

  // SRAM arbiter
  logic [31:0] mem_addr;
  logic        mem_req;
  logic        mem_write;
  logic  [3:0] mem_be;
  logic [31:0] mem_wdata;
  logic        mem_rvalid;
  logic [31:0] mem_rdata;


  ibex_core #(
     .RegFile(ibex_pkg::RegFileFPGA),
     .DmHaltAddr(32'h00000000),
     .DmExceptionAddr(32'h00000000)
  ) u_core (
     .clk_i                 (clk_sys),
     .rst_ni                (rst_sys_n),

     .test_en_i             ('b0),

     .hart_id_i             (32'b0),
     // First instruction executed is at 0x0 + 0x80
     .boot_addr_i           (32'h00000000),

     .instr_req_o           (instr_req),
     .instr_gnt_i           (instr_gnt),
     .instr_rvalid_i        (instr_rvalid),
     .instr_addr_o          (instr_addr),
     .instr_rdata_i         (instr_rdata),
     .instr_err_i           ('b0),

     .data_req_o            (data_req),
     .data_gnt_i            (data_gnt),
     .data_rvalid_i         (data_rvalid),
     .data_we_o             (data_we),
     .data_be_o             (data_be),
     .data_addr_o           (data_addr),
     .data_wdata_o          (data_wdata),
     .data_rdata_i          (data_rdata),
     .data_err_i            ('b0),

     .irq_software_i        (1'b0),
     .irq_timer_i           (1'b0),
     .irq_external_i        (1'b0),
     .irq_fast_i            (15'b0),
     .irq_nm_i              (1'b0),

     .debug_req_i           ('b0),

     .fetch_enable_i        ('b1),
     .alert_minor_o         (),
     .alert_major_o         (),
     .core_sleep_o          ()
  );

  // Connect Ibex to SRAM
  always_comb begin
    mem_req        = 1'b0;
    mem_addr       = 32'b0;
    mem_write      = 1'b0;
    mem_be         = 4'b0;
    mem_wdata      = 32'b0;
    if (instr_req) begin
      mem_req        = (instr_addr & ~MEM_MASK) == MEM_START;
      mem_addr       = instr_addr;
    end else if (data_req) begin
      mem_req        = (data_addr & ~MEM_MASK) == MEM_START;
      mem_write      = data_we;
      mem_be         = data_be;
      mem_addr       = data_addr;
      mem_wdata      = data_wdata;
    end
  end

  // SRAM block for instruction and data storage
  ram_1p #(
    .Depth(MEM_SIZE / 4),
    .MemInitFile(SRAMInitFile)
  ) u_ram (
    .clk_i     ( clk_sys        ),
    .rst_ni    ( rst_sys_n      ),
    .req_i     ( mem_req        ),
    .we_i      ( mem_write      ),
    .be_i      ( mem_be         ),
    .addr_i    ( mem_addr       ),
    .wdata_i   ( mem_wdata      ),
    .rvalid_o  ( mem_rvalid     ),
    .rdata_o   ( mem_rdata      )
  );

  // SRAM to Ibex
  assign instr_rdata    = mem_rdata;
  assign data_rdata     = mem_rdata;
  assign instr_rvalid   = mem_rvalid;
  always_ff @(posedge clk_sys or negedge rst_sys_n) begin
    if (!rst_sys_n) begin
      instr_gnt    <= 'b0;
      data_gnt     <= 'b0;
      data_rvalid  <= 'b0;
    end else begin
      instr_gnt    <= instr_req && mem_req;
      data_gnt     <= ~instr_req && data_req && mem_req;
      data_rvalid  <= ~instr_req && data_req && mem_req;
    end
  end

  // Connect the LED output to the lower four bits of the most significant
  // byte
  logic [3:0] leds;
  always_ff @(posedge clk_sys or negedge rst_sys_n) begin
    if (!rst_sys_n) begin
      leds <= 4'b0;
    end else begin
      if (mem_req && data_req && data_we) begin
        for (int i = 0; i < 4; i = i + 1) begin
          if (data_be[i] == 1'b1) begin
            leds <= data_wdata[i*8 +: 4];
          end
        end
      end
    end
  end
  assign LED = leds;

  // Clock and reset
  clkgen_xil7series
    clkgen(
      .IO_CLK,
      .IO_RST_N,
      .clk_sys,
      .rst_sys_n
    );

endmodule
