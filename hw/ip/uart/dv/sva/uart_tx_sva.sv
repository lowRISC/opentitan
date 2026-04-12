// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SVA assertions for uart_tx module
// Contributor: Angad Singh

module uart_tx_sva (
  input clk_i,
  input rst_ni,
  input tx_enable,
  input tx,
  input idle,
  input [3:0] bit_cnt_q,
  input parity_enable,
  input wr
);

  // Rule 1: After reset, TX must be HIGH (idle state)
  property tx_high_after_reset;
    @(posedge clk_i)
    !rst_ni |-> tx == 1'b1;
  endproperty
  assert property (tx_high_after_reset)
    else $error("FAIL: TX not HIGH during reset");

  // Rule 2: When TX is disabled, TX wire must be HIGH
  property tx_high_when_disabled;
    @(posedge clk_i) disable iff (!rst_ni)
    !tx_enable |-> tx == 1'b1;
  endproperty
  assert property (tx_high_when_disabled)
    else $error("FAIL: TX not HIGH when disabled");

  // Rule 3: When idle, bit counter must be zero
  property idle_means_zero_bitcnt;
    @(posedge clk_i) disable iff (!rst_ni)
    (tx_enable && idle) |-> (bit_cnt_q == 4'h0);
  endproperty
  assert property (idle_means_zero_bitcnt)
    else $error("FAIL: idle HIGH but bit counter not zero");

  // Rule 4: New write should only happen when idle
  property write_only_when_idle;
    @(posedge clk_i) disable iff (!rst_ni)
    wr |-> idle;
  endproperty
  assert property (write_only_when_idle)
    else $error("FAIL: write attempted when not idle");

endmodule
