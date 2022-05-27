// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bound into the otbn_controller and used to help collect ISPR information for coverage.

interface otbn_controller_if
  import otbn_pkg::*;
(
  input         clk_i,
  input         rst_ni,

  // Signal names from the otbn_controller module (where we are bound)
  input logic [ExtWLEN-1:0]          ispr_rdata_intg_i,
  input logic [BaseWordsPerWLEN-1:0] ispr_read_mask,
  input logic                        non_prefetch_insn_running
);

  // Force the `ispr_rdata_intg_i` signal to `should_val`.  This function needs to be static because
  // its argument must live as least as long as the `force` statement is in effect.
  function static void force_ispr_rdata_intg_i(input logic [ExtWLEN-1:0] should_val);
    force u_otbn_controller.ispr_rdata_intg_i = should_val;
  endfunction

  // Release the forcing of the `ispr_rdata_intg_i` signal.
  function automatic void release_ispr_rdata_intg_i();
    release u_otbn_controller.ispr_rdata_intg_i;
  endfunction

  // Wait until some ISPR data is being used (outside a reset) or until `max_cycles` clock cycles
  // have passed. When this task returns, the `success` output is set to `1'b1` if the data is being
  // used and to `1'b0` otherwise.
  task automatic wait_for_ispr_rdata_used(input int unsigned max_cycles, output bit success);
    int unsigned cycle_cnt = 0;
    while (1) begin
      @(negedge clk_i);
      if (rst_ni && |ispr_read_mask && non_prefetch_insn_running) begin
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
