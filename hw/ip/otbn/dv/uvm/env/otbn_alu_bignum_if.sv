// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bound into the otbn_alu_bignum and used to help collect ISPR information for coverage.

interface otbn_alu_bignum_if (
  input         clk_i,
  input         rst_ni,

  input [otbn_pkg::ExtWLEN-1:0] mod_intg_q,
  input                         mod_used
);

  // Force the `mod_intg_q` register to `should_val`.  This function needs to be static because its
  // argument must live as least as long as the `force` statement is in effect.
  function static void force_mod_intg_q(input logic [otbn_pkg::ExtWLEN-1:0] should_val);
    force u_otbn_alu_bignum.mod_intg_q = should_val;
  endfunction

  // Release the forcing of the `mod_intg_q` register.
  function automatic void release_mod_intg_q();
    release u_otbn_alu_bignum.mod_intg_q;
  endfunction

  // Wait for the `mod_used` signal to be high (outside a reset) or until `max_cycles` clock cycles
  // have passed.  When this task returns, the `success` output is set to `1'b1` if the `mod_used`
  // signal was high and to `1'b0` otherwise.
  task automatic wait_for_mod_used(input int unsigned max_cycles, output bit success);
    int unsigned cycle_cnt = 0;
    while (1) begin
      @(negedge clk_i);
      if (rst_ni && mod_used) begin
        success = 1'b1;
        break;
      end
      if (max_cycles != 0 && cycle_cnt >= max_cycles) begin
        success = 1'b0;
        break;
      end
      cycle_cnt++;
    end
  endtask

endinterface
