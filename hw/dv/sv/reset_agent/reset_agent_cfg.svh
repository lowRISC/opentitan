// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class reset_agent_cfg extends dv_base_agent_cfg;
  `uvm_object_utils(reset_agent_cfg)

  virtual reset_if vif;

  // Non-functional configuration knobs
  bit enable_debug_messages   = 0;    // Makes this agent talkative for debugging purposes

  // Functional configuration knobs
  polarity_e  polarity;           // Reset polarity: ActiveLow / ActiveHigh
  bit         assert_is_sync;     // Reset assertion should be synchronous to the input clock
  bit         deassert_is_sync;   // Reset deassertion should be synchronous to the input clock

  // Standard SV/UVM methods
  extern function new(string name = "");
endclass : reset_agent_cfg


function reset_agent_cfg::new(string name = "");
  super.new(name);
endfunction : new
