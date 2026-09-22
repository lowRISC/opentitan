// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Like kmac_app_rsp_ready_always_policy, but rsp_ready dips low for one cycle immediately after
// each rsp_valid/rsp_ready handshake completes, before going back high.
class kmac_app_rsp_ready_always_with_dip_policy extends kmac_app_rsp_ready_policy;
  `uvm_object_utils(kmac_app_rsp_ready_always_with_dip_policy)

  local bit prev_rsp_valid;
  local bit prev_ready;

  extern function new(string name = "");
  extern virtual function void reset();
  extern virtual function bit get_rsp_ready(bit rsp_valid,
                                            int unsigned ready_pct,
                                            int unsigned max_stall_cycles);
endclass

function kmac_app_rsp_ready_always_with_dip_policy::new(string name = "");
  super.new(name);
endfunction

function void kmac_app_rsp_ready_always_with_dip_policy::reset();
  prev_rsp_valid = 0;
  prev_ready = 0;
endfunction

function bit kmac_app_rsp_ready_always_with_dip_policy::get_rsp_ready(
    bit rsp_valid,
    int unsigned ready_pct,
    int unsigned max_stall_cycles);
  // A handshake completed on the previous cycle if rsp_valid and rsp_ready were both high then.
  bit ready = (prev_rsp_valid && prev_ready) ? 1'b0 : 1'b1;

  prev_rsp_valid = rsp_valid;
  prev_ready = ready;
  return ready;
endfunction
