// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Virtual base class used for alert and escalation drivers
//
// This is essentially just a wrapper around dv_base_driver but supplies the item type
// parameterisation, which allows us to define a type name. This means that it can be registered
// properly with the factory.

class alert_esc_base_driver extends dv_base_driver#(alert_esc_seq_item, alert_esc_agent_cfg);
  `uvm_component_utils(alert_esc_base_driver)

  extern function new (string name, uvm_component parent);
endclass

function alert_esc_base_driver::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction
