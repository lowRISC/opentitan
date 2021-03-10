// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_sequencer extends dv_base_sequencer #(
    .ITEM_T (keymgr_kmac_item),
    .CFG_T  (keymgr_kmac_agent_cfg)
);
  `uvm_component_param_utils(keymgr_kmac_sequencer)

  push_pull_sequencer#(`CONNECT_DATA_WIDTH) m_push_pull_sequencer;

  `uvm_component_new

endclass
