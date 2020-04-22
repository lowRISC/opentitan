// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_driver #(type ITEM_T     = uvm_sequence_item,
                       type CFG_T      = dv_base_agent_cfg,
                       type RSP_ITEM_T = ITEM_T)
  extends uvm_driver #(.REQ(ITEM_T), .RSP(RSP_ITEM_T));

  `uvm_component_param_utils(dv_base_driver #(.ITEM_T     (ITEM_T),
                                              .CFG_T      (CFG_T),
                                              .RSP_ITEM_T (RSP_ITEM_T)))

  bit   under_reset;
  CFG_T cfg;

  `uvm_component_new

  virtual task run_phase(uvm_phase phase);
    fork
      reset_signals();
      get_and_drive();
    join
  endtask

  // reset signals
  virtual task reset_signals();
    `uvm_fatal(`gfn, "this is implemented as pure virtual task - please extend")
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    `uvm_fatal(`gfn, "this is implemented as pure virtual task - please extend")
  endtask

endclass

