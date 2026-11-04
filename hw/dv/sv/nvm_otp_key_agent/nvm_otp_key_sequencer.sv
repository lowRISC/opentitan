// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class nvm_otp_key_sequencer extends dv_reactive_sequencer #(
  .ITEM_T (nvm_otp_key_item),
  .CFG_T  (nvm_otp_key_agent_cfg)
);
  `uvm_component_utils(nvm_otp_key_sequencer)

  extern function new(string name, uvm_component parent);
endclass : nvm_otp_key_sequencer

function nvm_otp_key_sequencer::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new
