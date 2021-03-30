// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_sequencer #(type ITEM_T     = uvm_sequence_item,
                          type CFG_T      = dv_base_agent_cfg,
                          type RSP_ITEM_T = ITEM_T)
  extends uvm_sequencer #(.REQ(ITEM_T), .RSP(RSP_ITEM_T));

  `uvm_component_param_utils(dv_base_sequencer #(.ITEM_T     (ITEM_T),
                                                 .CFG_T      (CFG_T),
                                                 .RSP_ITEM_T (RSP_ITEM_T)))

  CFG_T cfg;

  `uvm_component_new

endclass
