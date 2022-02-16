// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class key_sideload_sequencer #(
    parameter type KEY_T = keymgr_pkg::hw_key_req_t
)  extends dv_base_sequencer #(
    .ITEM_T (key_sideload_item#(KEY_T)),
    .CFG_T  (key_sideload_agent_cfg#(KEY_T))
);
  `uvm_component_param_utils(key_sideload_sequencer#(KEY_T))
  `uvm_component_new

endclass
