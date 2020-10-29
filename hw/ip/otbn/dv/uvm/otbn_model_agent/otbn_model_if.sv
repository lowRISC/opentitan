// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface otbn_model_if #(
  // Size of the instruction memory, in bytes
  parameter int ImemSizeByte = 4096,

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte)
) (
  input logic clk_i,
  input logic rst_ni
);

  logic                     start;        // Start the operation
  logic [ImemAddrWidth-1:0] start_addr;   // Start byte address in IMEM

  bit                       done;         // Operation done
  bit                       err;          // Something went wrong

  // Wait until done goes high. Stops early on reset
  task automatic wait_done();
    while (rst_ni === 1'b1 && !done) begin
      @(posedge clk_i or negedge rst_ni);
    end
  endtask

  // Wait until done goes low. Stops early on reset
  task automatic wait_not_done();
    while (rst_ni === 1'b1 && done) begin
      @(posedge clk_i or negedge rst_ni);
    end
  endtask

  // Start model by setting start and start_addr for a cycle. Waits until not in reset.
  task automatic start_model(bit [ImemAddrWidth-1:0] start_addr);
    wait(rst_ni);
    start = 1'b1;
    start_addr = start_addr;
    @(posedge clk_i or negedge rst_ni);
    start = 1'b0;
    start_addr = 'x;
  endtask

  // The err signal is asserted by the model if it fails to find the DUT or if it finds a mismatch
  // in results. It should never go high.
  `ASSERT(NoModelErrs, !err)

endinterface
