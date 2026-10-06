// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Response-ready policy that accepts each response on the first cycle
// on which rsp_valid is seen.
//
// The policy asserts rsp_ready for exactly one cycle per response indication.
// If the DUT keeps rsp_valid asserted after that handshake,
// the policy keeps rsp_ready low until rsp_valid returns low.
class kmac_app_rsp_ready_when_valid_policy extends kmac_app_rsp_ready_policy;
  `uvm_object_utils(kmac_app_rsp_ready_when_valid_policy)

  // When rsp_valid first goes high, the policy accepts the response
  // for one cycle by setting rsp_ready.
  // If rsp_valid stays high afterward, it keeps rsp_ready low
  // until rsp_valid goes low again.
  local bit accepted;

  extern function new(string name = "");
  extern virtual function void reset();
  extern virtual function bit get_rsp_ready(bit rsp_valid,
					    int unsigned ready_pct,
					    int unsigned max_stall_cycles);
endclass

function kmac_app_rsp_ready_when_valid_policy::new(string name = "");
  super.new(name);
endfunction

// Clear the per-response state.
function void kmac_app_rsp_ready_when_valid_policy::reset();
  accepted = 0;
endfunction

// Assert ready once per rsp_valid assertion.
function bit
  kmac_app_rsp_ready_when_valid_policy::get_rsp_ready(bit          rsp_valid,
						      int unsigned ready_pct,
						      int unsigned max_stall_cycles);
  bit ready;

  // A low valid signal marks the end of the current response indication.
  // Clearing accepted here is what permits exactly one ready pulse
  // when the next response becomes valid.
  if (!rsp_valid) begin
    accepted = 0;
    ready = 0;
  end else if (accepted) begin
    // Prevent repeated acceptance while valid remains high.
    ready = 0;
  end else begin
    // Accept the first valid cycle.
    ready = 1;
    accepted = 1;
  end

  return ready;
endfunction
