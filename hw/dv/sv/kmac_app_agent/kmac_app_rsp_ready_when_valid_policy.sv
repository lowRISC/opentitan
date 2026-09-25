// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Assert rsp_ready for a single cycle when rsp_valid is first seen. If the DUT
// holds rsp_valid after the handshake, keep rsp_ready low until valid drops.
class kmac_app_rsp_ready_when_valid_policy extends kmac_app_rsp_ready_policy;
  `uvm_object_utils(kmac_app_rsp_ready_when_valid_policy)

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

function void kmac_app_rsp_ready_when_valid_policy::reset();
  accepted = 0;
endfunction

function bit kmac_app_rsp_ready_when_valid_policy::get_rsp_ready(
    bit rsp_valid,
    int unsigned ready_pct,
    int unsigned max_stall_cycles);
  bit ready;

  if (!rsp_valid) begin
    accepted = 0;
    ready = 0;
  end else if (accepted) begin
    ready = 0;
  end else begin
    ready = 1;
    accepted = 1;
  end

  return ready;
endfunction