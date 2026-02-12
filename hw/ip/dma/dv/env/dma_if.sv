// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import dma_pkg::*;

interface dma_if #(parameter int unsigned WIDTH_IN = dma_reg_pkg::NumIntClearSources);
logic [WIDTH_IN-1:0] handshake_i = '0;   // IO->DMA handshake signal

task automatic init();
  handshake_i <= '0;
endtask : init

endinterface
