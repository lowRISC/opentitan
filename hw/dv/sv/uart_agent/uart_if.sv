// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
interface uart_if #(time UartDefaultClkPeriodNs = 104166.667ns) ();
  logic uart_rx;
  logic uart_tx;
  logic uart_tx_en;

  // generate local clk
  time  uart_clk_period_ns = UartDefaultClkPeriodNs;
  bit   uart_tx_clk = 1'b1;
  int   uart_tx_clk_pulses = 0;
  bit   uart_rx_clk = 1'b1;
  int   uart_rx_clk_pulses = 0;

  clocking drv_tx_cb @(posedge uart_tx_clk);
    output uart_tx;
  endclocking
  modport drv_tx_mp(clocking drv_tx_cb);

  clocking mon_tx_cb @(negedge uart_tx_clk);
    input  #10ns uart_tx;
  endclocking
  modport mon_tx_mp(clocking mon_tx_cb);

  clocking drv_rx_cb @(posedge uart_rx_clk);
    output uart_rx;
  endclocking
  modport drv_rx_mp(clocking drv_rx_cb);

  clocking mon_rx_cb @(negedge uart_rx_clk);
    input  #10ns uart_rx;
  endclocking
  modport mon_rx_mp(clocking mon_rx_cb);

  // Generate the uart_*x_clk, with UartDefaultClkPeriodNs period as default
  // Clock pulses are generated when is greater than zero, so for the driver or the monitor
  // to generate their trigger events, they set i to generate the number of pulses they need.
  initial begin
    uart_tx_clk = 1'b1;
    uart_rx_clk = 1'b1;
    fork
      forever begin
        if (uart_tx_clk_pulses > 0) begin
          #(uart_clk_period_ns/2);
          uart_tx_clk = ~uart_tx_clk;
          #(uart_clk_period_ns/2);
          uart_tx_clk = ~uart_tx_clk;
          uart_tx_clk_pulses--;
        end else begin
          @(uart_tx, uart_tx_clk_pulses);
        end
      end
      forever begin
        if (uart_rx_clk_pulses > 0) begin
          #(uart_clk_period_ns/2);
          uart_rx_clk = ~uart_rx_clk;
          #(uart_clk_period_ns/2);
          uart_rx_clk = ~uart_rx_clk;
          uart_rx_clk_pulses--;
        end else begin
          @(uart_rx, uart_rx_clk_pulses);
        end
      end
    join
  end

  task automatic wait_for_tx_idle();
    wait(uart_tx_clk_pulses == 0);
  endtask

  task automatic wait_for_rx_idle();
    wait(uart_rx_clk_pulses == 0);
  endtask

  task automatic wait_for_idle();
    fork
      wait_for_tx_idle();
      wait_for_rx_idle();
    join
  endtask

  task automatic drive_uart_rx_glitch(int max_glitch_ps, int stable_ps_after_glitch);
    uart_rx = ~uart_rx;
    randcase
      1: #(max_glitch_ps * 1ps);
      1: #($urandom_range(1, max_glitch_ps) * 1ps);
    endcase
    uart_rx = ~uart_rx;
    #(stable_ps_after_glitch * 1ps);
  endtask

endinterface
