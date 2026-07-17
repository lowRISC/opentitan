// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that should be bound into an instance of prim_sync_reqack_data and can be used to
// control its assertions.
//
// This should only be registered with an environment indirectly (through u_pins_if), which avoids
// elaboration errors that would be caused otherwise by using the interface type when there is no
// binding (and the upwards hierarchical reference cannot work)

interface reqack_data_if ();
  import uvm_pkg::*;

  // If this flag becomes true, we will use a force statement to force a chk_flag signal.
  wire assertions_disabled;

  // Drive assertions_disabled with a single output pin. This pins interface can be exposed to e.g.
  // a block-level environment, which can use its type even if reqack_data_if isn't actually bound
  // anywhere (avoiding elaboration errors from the hierarchical reference in that case).
  pins_if #(.Width(1)) u_pins_if (.pins(assertions_disabled));

  // A flag that tracks whether the interface has used a force statement to hold effective_rst_n=0.
  bit has_force = 0;

  always @(assertions_disabled) begin
    if (assertions_disabled) begin
      if (!has_force) begin
        `uvm_info($sformatf("%m"), "Disabling reqack assertions", UVM_HIGH)
        force u_prim_sync_reqack.effective_rst_n = 0;
        has_force = 1;
      end
    end else begin
      if (has_force) begin
        `uvm_info($sformatf("%m"), "Re-enabling reqack assertions", UVM_HIGH)
        release u_prim_sync_reqack.effective_rst_n;
        has_force = 0;
      end
    end
  end
endinterface
