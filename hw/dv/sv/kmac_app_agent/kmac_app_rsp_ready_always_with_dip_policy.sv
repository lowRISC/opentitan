// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Response-ready policy that keeps rsp_ready asserted by default and inserts a one-cycle dip after
// every completed response handshake.
//
// Compared with kmac_app_rsp_ready_always_policy, this policy deliberately deasserts rsp_ready for
// one cycle after rsp_valid and rsp_ready were both high.
class kmac_app_rsp_ready_always_with_dip_policy extends kmac_app_rsp_ready_policy;
  `uvm_object_utils(kmac_app_rsp_ready_always_with_dip_policy)

  // Previous-cycle rsp_valid, used to detect a completed handshake.
  local bit prev_rsp_valid;

  // Previous-cycle ready decision.
  local bit prev_ready;

  extern function new(string name = "");
  extern virtual function void reset();
  extern virtual function bit get_rsp_ready(bit 	 rsp_valid,
					    int unsigned ready_pct,
					    int unsigned max_stall_cycles);
endclass

function kmac_app_rsp_ready_always_with_dip_policy::new(string name = "");
  super.new(name);
endfunction

// Clear previous-cycle handshake state.
function void kmac_app_rsp_ready_always_with_dip_policy::reset();
  prev_rsp_valid = 0;
  prev_ready = 0;
endfunction

// Return ready, with a one-cycle dip after each handshake.
function bit
  kmac_app_rsp_ready_always_with_dip_policy::get_rsp_ready(bit          rsp_valid,
							   int unsigned ready_pct,
							   int unsigned max_stall_cycles);

  // Dip only after valid and ready were both high in the previous cycle.
  bit ready = (prev_rsp_valid && prev_ready) ? 1'b0 : 1'b1;

  // Save state for the next cycle.
  prev_rsp_valid = rsp_valid;
  prev_ready = ready;
  return ready;
endfunction
