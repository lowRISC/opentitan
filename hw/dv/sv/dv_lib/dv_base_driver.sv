// Copyright lowRISC contributors (OpenTitan project).
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
    wait(under_reset);
    forever begin
      wait(!under_reset);
      // This isolation fork is needed to ensure that "disable fork" call won't kill any other
      // processes at the same level from the base classes
      fork begin : isolation_fork
        fork
          begin : main_thread
            fork
              reset_signals();
              get_and_drive();
            join
            wait fork;  // To ensure it will be killed only when the reset will occur
          end
          begin : reset_thread
            wait(under_reset);
          end
        join_any
        disable fork;   // Terminates all descendants and sub-descendants of isolation_fork
      end join
    end
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
