// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_error_log_sequencer extends dv_base_sequencer#(.ITEM_T (racl_error_log_vec_driver_item),
                                                          .CFG_T  (racl_error_log_agent_cfg));
  `uvm_component_utils(racl_error_log_sequencer)

  extern function new (string name, uvm_component parent);
endclass

function racl_error_log_sequencer::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction
