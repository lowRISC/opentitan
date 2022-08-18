// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bound into the otbn_mac_bignum and used to help collect ISPR information for coverage.

interface otbn_mac_bignum_if (
  input         clk_i,
  input         rst_ni,

  // Signal names from the otbn_mac_bignum module (where we are bound)
  input logic [255:0]                 adder_op_a,
  input logic [255:0]                 adder_op_b,
  input logic [otbn_pkg::ExtWLEN-1:0] acc_intg_q,
  input logic                         acc_used
);

  // Return the intermediate sum (the value of ACC before it gets truncated back down to 256 bits).
  function automatic logic [256:0] get_sum_value();
    return {1'b0, adder_op_a} + {1'b0, adder_op_b};
  endfunction

  // Force the `acc_intg_q` register to `should_val`.  This function needs to be static because its
  // argument must live as least as long as the `force` statement is in effect.
  function static void force_acc_intg_q(input logic [otbn_pkg::ExtWLEN-1:0] should_val);
    force u_otbn_mac_bignum.acc_intg_q = should_val;
  endfunction

  // Release the forcing of the `acc_intg_q` register.
  function automatic void release_acc_intg_q();
    release u_otbn_mac_bignum.acc_intg_q;
  endfunction

  // Wait for the `acc_used` signal to be high (outside a reset) or until `max_cycles` clock cycles
  // have passed.  When this task returns, the `used_words` output indicates which words are being
  // used.
  task automatic wait_for_acc_used(input int unsigned max_cycles,
                                   output bit [otbn_pkg::BaseWordsPerWLEN-1:0] used_words);
    int unsigned cycle_cnt = 0;
    while (1) begin
      @(negedge clk_i);
      if (rst_ni && acc_used) begin
        used_words = '1;
        break;
      end
      if (max_cycles != 0 && cycle_cnt >= max_cycles) begin
        used_words = '0;
        break;
      end
      cycle_cnt++;
    end
  endtask

endinterface
