// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import dma_pkg::*;

interface dma_if #(parameter uint WIDTH_IN = dma_pkg::NUM_LSIO_TRIGGERS) (
  input clk_i,
  input rst_ni
);

logic [WIDTH_IN-1:0] handshake_i = '0;   // IO->DMA handshake signal
logic [31:0]         remaining;
// For DMA handshake mode, we are expected to manage lsio_trigger_i.
logic                read_cmpl_host;
logic                read_cmpl_ctn;  //  Due to the above requirement we need to track FIFO drain
logic                read_opc_host;
logic                read_opc_ctn;

task automatic init();
  handshake_i <= '0;
endtask : init

// Drive Handshake
task automatic drive(input int pos = 0);
  handshake_i[pos] <= 1'b1;
endtask : drive

endinterface
