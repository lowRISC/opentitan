// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_xht_sequencer extends dv_base_sequencer #(
    .ITEM_T (entropy_src_xht_item),
    .CFG_T  (entropy_src_xht_agent_cfg)
);
  `uvm_component_utils(entropy_src_xht_sequencer)
  `uvm_component_new

endclass
