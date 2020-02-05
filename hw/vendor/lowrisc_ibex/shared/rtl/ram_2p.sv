// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Dual-port RAM with 1 cycle read/write delay, 32 bit words.
 *
 * The two ports are in Read-First Mode: when reading from and writing to the same address
 * simultaneously, the old content is returned, before the new content is written. New content
 * is made available to both ports with one cycle delay.
 *
 * Simultaneous write operations by both ports to the same address are to be avoided: The data
 * written to memory is not determined.
 */
module ram_2p #(
    parameter int Depth = 128
) (
    input               clk_i,
    input               rst_ni,

    input               a_req_i,
    input               a_we_i,
    input        [ 3:0] a_be_i,
    input        [31:0] a_addr_i,
    input        [31:0] a_wdata_i,
    output logic        a_rvalid_o,
    output logic [31:0] a_rdata_o,

    input               b_req_i,
    input               b_we_i,
    input        [ 3:0] b_be_i,
    input        [31:0] b_addr_i,
    input        [31:0] b_wdata_i,
    output logic        b_rvalid_o,
    output logic [31:0] b_rdata_o
);

  localparam int Aw = $clog2(Depth);

  logic [31:0] mem [Depth];

  logic [Aw-1:0] a_addr_idx;
  assign a_addr_idx = a_addr_i[Aw-1+2:2];
  logic [31-Aw:0] unused_a_addr_parts;
  assign unused_a_addr_parts = {a_addr_i[31:Aw+2], a_addr_i[1:0]};

  logic [Aw-1:0] b_addr_idx;
  assign b_addr_idx = b_addr_i[Aw-1+2:2];
  logic [31-Aw:0] unused_b_addr_parts;
  assign unused_b_addr_parts = {b_addr_i[31:Aw+2], b_addr_i[1:0]};

  always @(posedge clk_i) begin
    if (a_req_i) begin
      if (a_we_i) begin
        for (int i = 0; i < 4; i = i + 1) begin
          if (a_be_i[i] == 1'b1) begin
            mem[a_addr_idx][i*8 +: 8] <= a_wdata_i[i*8 +: 8];
          end
        end
      end
      a_rdata_o <= mem[a_addr_idx];
    end
  end

  always @(posedge clk_i) begin
    if (b_req_i) begin
      if (b_we_i) begin
        for (int i = 0; i < 4; i = i + 1) begin
          if (b_be_i[i] == 1'b1) begin
            mem[b_addr_idx][i*8 +: 8] <= b_wdata_i[i*8 +: 8];
          end
        end
      end
      b_rdata_o <= mem[b_addr_idx];
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      a_rvalid_o <= '0;
    end else begin
      a_rvalid_o <= a_req_i;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      b_rvalid_o <= '0;
    end else begin
      b_rvalid_o <= b_req_i;
    end
  end

  `ifdef VERILATOR
    // Task for loading 'mem' with SystemVerilog system task $readmemh()
    export "DPI-C" task simutil_verilator_memload;
    // Function for setting a specific 32 bit element in |mem|
    // Returns 1 (true) for success, 0 (false) for errors.
    export "DPI-C" function simutil_verilator_set_mem;

    task simutil_verilator_memload;
      input string file;
      $readmemh(file, mem);
    endtask

    // TODO: Allow 'val' to have other widths than 32 bit
    function int simutil_verilator_set_mem(input int index,
                                           input logic[31:0] val);
      if (index >= Depth) begin
        return 0;
      end

      mem[index] = val;
      return 1;
    endfunction
  `endif

  `ifdef SRAM_INIT_FILE
    localparam MEM_FILE = `"`SRAM_INIT_FILE`";
    initial begin
      $display("Initializing SRAM from %s", MEM_FILE);
      $readmemh(MEM_FILE, mem);
    end
  `endif
endmodule
