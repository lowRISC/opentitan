// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface irq_if(input clk);
  logic        reset;
  logic        irq_software;
  logic        irq_timer;
  logic        irq_external;
  logic [14:0] irq_fast;
  logic        irq_nm;       // non-maskeable interrupt

  clocking driver_cb @(posedge clk);
    default output negedge;
    input   reset;
    output  irq_software;
    output  irq_timer;
    output  irq_external;
    output  irq_fast;
    output  irq_nm;
  endclocking

  clocking monitor_cb @(posedge clk);
    input reset;
    input irq_software;
    input irq_timer;
    input irq_external;
    input irq_fast;
    input irq_nm;
  endclocking

  task automatic wait_clks(input int num);
    repeat (num) @(posedge clk);
  endtask

  task automatic wait_neg_clks(input int num);
    repeat (num) @(negedge clk);
  endtask

endinterface
