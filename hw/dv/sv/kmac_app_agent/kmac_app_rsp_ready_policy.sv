// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Base class for response backpressure policies used by the KMAC app host driver.
//
// The driver owns the handshake logic and calls a policy object every cycle to decide whether to
// assert rsp_ready. This abstraction lets multiple response behaviors share the same interface while
// keeping the driver logic independent from the policy implementation. A pure virtual interface is
// used here so every concrete policy must implement the same contract: reset the state on reset and
// decide the ready signal based on rsp_valid, ready_pct, and max_stall_cycles.
virtual class kmac_app_rsp_ready_policy extends uvm_object;

  extern function new(string name = "");

  // Reset policy state before response processing resumes.
  pure virtual function void reset();

  // Return the rsp_ready decision for the current cycle.
  pure virtual function bit get_rsp_ready(bit rsp_valid, 
                                          int unsigned ready_pct, 
                                          int unsigned max_stall_cycles);
endclass

function kmac_app_rsp_ready_policy::new(string name = "");
  super.new(name);
endfunction
