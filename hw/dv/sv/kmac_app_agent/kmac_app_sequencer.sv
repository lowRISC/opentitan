// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_sequencer extends dv_base_sequencer #(
    .ITEM_T (kmac_app_item),
    .CFG_T  (kmac_app_agent_cfg)
);
  `uvm_component_utils(kmac_app_sequencer)

  push_pull_sequencer#(`CONNECT_DATA_WIDTH) m_push_pull_sequencer;

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass
