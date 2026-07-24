// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// An interface that should be bound into an instance of keymgr_dpe_ctrl (and can access RTL signals
// through upwards hierarchical references).
interface keymgr_dpe_ctrl_if (input clk_i, input rst_ni);
  import uvm_pkg::*;

  // Function to access the key of one slot via backdoor.
  // Required to load the UDS after XORing with generated randomness.
  function automatic keymgr_dpe_env_pkg::key_shares_t get_key_of_slot(int unsigned slot);
    import keymgr_dpe_env_pkg::DvNumInstHwSlot;

    // Check that the slot index is in range. The key_slots_q array has length DvNumInstHwSlot,
    // which is a global parameter.
    if (slot >= DvNumInstHwSlot) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Slot index out of range: index is %0d but DvNumInstHwSlot is %0d",
                           slot, DvNumInstHwSlot))
      return '0;
    end

    // This is an upwards hierarchical reference through the keymgr_dpe_ctrl module (into an
    // instance of which this interface is bound)
    return keymgr_dpe_ctrl.key_slots_q[slot].key;
  endfunction
endinterface
