// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SVA assertions for uart_tx module
// Contributor: Angad Singh

module uart_tx_sva (
  input logic clk_i,
  input logic rst_ni,
  input logic tx_enable_i,
  input logic tx_o,
  input logic idle_o,
  input logic [3:0] bit_cnt_q,
  input logic parity_enable_i,
  input logic wr_i
);

  default clocking @(posedge clk_i); endclocking
  default disable iff (!rst_ni);

  // Rule 1: After reset, TX must be HIGH (idle state)
  property tx_high_after_reset;
    !rst_ni |-> tx_o == 1'b1;
  endproperty
  TxHighAfterReset_A: assert property (tx_high_after_reset)
    else `ASSERT_ERROR(TxHighAfterReset_A);

  // Rule 2: When TX is disabled, TX wire must be HIGH
  property tx_high_when_disabled;
    !tx_enable_i |-> tx_o == 1'b1;
  endproperty
  TxHighWhenDisabled_A: assert property (tx_high_when_disabled)
    else `ASSERT_ERROR(TxHighWhenDisabled_A);

  // Rule 3: When idle, bit counter must be zero
  // This checks internal consistency: idle is defined as
  // bit_cnt_q == 0 when enabled, so this should always hold.
  property idle_means_zero_bitcnt;
    (tx_enable_i && idle_o) |-> (bit_cnt_q == 4'h0);
  endproperty
  IdleMeansZeroBitcnt_A: assert property (idle_means_zero_bitcnt)
    else `ASSERT_ERROR(IdleMeansZeroBitcnt_A);

  // Rule 4: New write should only happen when idle.
  // Note: this constrains the behaviour of an input port (wr_i),
  // not the internal design of this module. It documents the
  // expected usage protocol for callers of uart_tx.
  property write_only_when_idle;
    wr_i |-> idle_o;
  endproperty
  WriteOnlyWhenIdle_A: assert property (write_only_when_idle)
    else `ASSERT_ERROR(WriteOnlyWhenIdle_A);

endmodule
