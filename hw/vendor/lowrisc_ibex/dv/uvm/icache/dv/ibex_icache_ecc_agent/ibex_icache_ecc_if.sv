// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that gets bound into a badbit_ram_1p with .*

interface ibex_icache_ecc_if
  (input logic          clk_i,
   input logic          req_i,
   input logic          write_i,
   input logic [31:0]   width,
   input logic [31:0]   addr,
   input logic [127:0]  wdata,
   input logic [127:0]  wmask,
   input logic [127:0]  rdata,

   output logic [127:0] bad_bit_mask);

  // SVA module
  ibex_icache_ecc_protocol_checker checker_i (.*);

  // The address for the last monitored req transaction
  logic [31:0]  last_addr = 'x;

  bit rst_n = 1'b1;

  // Start a process that will drive the rst_n line low until the next clock, but return
  // immediately. If rst_n is already low, does nothing.
  task automatic reset();
    if (!rst_n) return;
    rst_n = 1'b0;
    fork
      begin
        @(posedge clk_i);
        rst_n = 1'b1;
      end
    join_none
  endtask

  // Wait until a cycle with req_i & ~write_i (signalling the start of a read).
  //
  // Returns early on reset.
  task automatic wait_for_read_start();
    while (rst_n && !(req_i & ~write_i)) @(posedge clk_i);
  endtask

  // Wait for num_reads complete reads. Ends on the clock posedge where the last read's data is
  // returned.
  //
  // Returns early on reset.
  task automatic wait_reads(int unsigned num_reads);
    repeat (num_reads) begin
      wait_for_read_start();
      if (!rst_n) break;
      @(posedge clk_i);
    end
  endtask

  // Set a bit to be toggled on the next read
  task static corrupt_read_1(int unsigned pos);
    wait_for_read_start();
    if (!rst_n) return;

    bad_bit_mask = 128'b1 << (pos % width);
    @(posedge clk_i);
    bad_bit_mask = 0;
  endtask

  // Set two bits to be toggled on the next read
  task static corrupt_read_2(int unsigned pos0, int unsigned pos1);
    wait_for_read_start();
    if (!rst_n) return;

    bad_bit_mask = (128'b1 << (pos0 % width)) | (128'b1 << (pos1 % width));
    @(posedge clk_i);
    bad_bit_mask = 0;
  endtask

  // Wait for a read, setting last_addr accordingly.
  //
  // This can be called re-entrantly, despite writing last_addr (it will just write the same value
  // more than once).
  //
  // Returns early on reset.
  task automatic wait_read();
    wait_for_read_start();
    if (!rst_n) return;
    last_addr = addr;
    @(posedge clk_i);
  endtask

  initial begin
    bad_bit_mask = 0;
  end

endinterface
