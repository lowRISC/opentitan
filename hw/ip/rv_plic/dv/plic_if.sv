// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

interface plic_if#(
  parameter N_SOURCE = 32
) (input clk, input rst_n);

  logic irq;
  logic [$clog2(N_SOURCE+1)-1:0] irq_id;

  modport tb (input clk, rst_n, irq, irq_id);
  modport dut(input clk, rst_n, output irq, irq_id);

endinterface : plic_if
