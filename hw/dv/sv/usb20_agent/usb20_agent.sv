// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_agent extends dv_base_agent #(
  .CFG_T          (usb20_agent_cfg),
  .DRIVER_T       (usb20_driver),
  .SEQUENCER_T    (usb20_sequencer),
  .MONITOR_T      (usb20_monitor),
  .COV_T          (usb20_agent_cov)
);
`uvm_component_utils(usb20_agent)

`uvm_component_new

function void build_phase(uvm_phase phase);
  super.build_phase(phase);
  // get usb20_block_if handle
  if (!uvm_config_db#(virtual usb20_block_if)::get(this, "", "bif", cfg.bif)) begin
    `uvm_fatal(`gfn, "failed to get usb20_block_if handle from uvm_config_db")
  end
endfunction

endclass
