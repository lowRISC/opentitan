// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

virtual class kmac_app_rsp_ready_policy extends uvm_object;

  extern function new(string name = "");

  pure virtual function void reset();
  pure virtual function bit get_rsp_ready(bit rsp_valid,
                                          int unsigned ready_pct,
                                          int unsigned max_stall_cycles);
endclass

function kmac_app_rsp_ready_policy::new(string name = "");
  super.new(name);
endfunction