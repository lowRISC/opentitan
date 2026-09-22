// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_rsp_ready_always_policy extends kmac_app_rsp_ready_policy;
  `uvm_object_utils(kmac_app_rsp_ready_always_policy)

  extern function new(string name = "");
  extern virtual function void reset();
  extern virtual function bit get_rsp_ready(bit rsp_valid,
                                            int unsigned ready_pct,
                                            int unsigned max_stall_cycles);
endclass

function kmac_app_rsp_ready_always_policy::new(string name = "");
  super.new(name);
endfunction

function void kmac_app_rsp_ready_always_policy::reset();
endfunction

function bit kmac_app_rsp_ready_always_policy::get_rsp_ready(
    bit rsp_valid,
    int unsigned ready_pct,
    int unsigned max_stall_cycles);
  return 1'b1;
endfunction