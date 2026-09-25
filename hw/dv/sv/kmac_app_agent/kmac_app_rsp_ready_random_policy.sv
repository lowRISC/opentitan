// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_rsp_ready_random_policy extends kmac_app_rsp_ready_policy;
  `uvm_object_utils(kmac_app_rsp_ready_random_policy)

  int unsigned stall_cycles;

  extern function new(string name = "");
  extern virtual function void reset();
  extern virtual function bit get_rsp_ready(bit rsp_valid,
                                            int unsigned ready_pct,
                                            int unsigned max_stall_cycles);
endclass

function kmac_app_rsp_ready_random_policy::new(string name = "");
  super.new(name);
endfunction

function void kmac_app_rsp_ready_random_policy::reset();
  stall_cycles = 0;
endfunction

function bit kmac_app_rsp_ready_random_policy::get_rsp_ready(
    bit rsp_valid,
    int unsigned ready_pct,
    int unsigned max_stall_cycles);
  bit ready;

  if (!rsp_valid) begin
    stall_cycles = 0;
    return 1'b0;
  end
  if (stall_cycles >= max_stall_cycles) begin
    stall_cycles = 0;
    return 1'b1;
  end

  ready = $urandom_range(0, 99) < ready_pct;
  stall_cycles = ready ? 0 : stall_cycles + 1;
  return ready;
endfunction