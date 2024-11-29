// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Use this UVM macro as we may need to implement multiple uvm_analysis_imp, which means
// implemneting multiple write methods which is not possible with the same name.
`uvm_analysis_imp_decl(_drv_reset)

class dv_base_driver #(type ITEM_T     = uvm_sequence_item,
                       type CFG_T      = dv_base_agent_cfg,
                       type RSP_ITEM_T = ITEM_T)
  extends uvm_driver #(.REQ(ITEM_T), .RSP(RSP_ITEM_T));

  `uvm_component_param_utils(dv_base_driver #(.ITEM_T     (ITEM_T),
                                              .CFG_T      (CFG_T),
                                              .RSP_ITEM_T (RSP_ITEM_T)))

  CFG_T cfg;

  uvm_analysis_imp_drv_reset #(
    reset_state_e, dv_base_driver#(ITEM_T,CFG_T,RSP_ITEM_T)) reset_st_imp;

  // TODO MVy: some drivers extended from this class are also declaring this bit and managing it,
  // so it should be removed from these child-classes as the configuration class is already
  // providing a similar information. There is also probably some methods which can be removed then.
  bit under_reset;


  function new (string name="", uvm_component parent=null);
    super.new(name, parent);
    reset_st_imp = new ("reset_st_imp", this);
  endfunction : new

  virtual task run_phase(uvm_phase phase);
    // After each reset, the current transaction should be dropped and get_and_drive should be
    // restarted once the reset is being deasserted.
    forever begin
      // This isolation fork is needed to ensure that "disable fork" call won't kill any other
      // processes at the same level from the base classes
      fork begin : isolation_fork
        fork
          begin : reset_signals_thread
            // TODO MVy: reset_signals should probably be a function. This should also be changed
            // in all the child classes. Meanwhile, spawn an unblocking thread. Instead of doing this
            // in the future we'll be able to only call this reset_signals function, which will be
            // implemented by all the extended drivers to actually act on the interface level as
            // required. It would be great to uniformise this as some drivers are doing to in different
            // ways, via different tasks/functions: invalidate_signals, do_reset_signals, do_reset...
            // Additionnally, each drivers should drop the reset management tasks: reset_thread,
            // reset_signals...
            reset_signals();
            wait(0);  // Wait indefinitely to ensure the fork will end because of a reset detection
          end
          begin : main_thread
            get_and_drive();
            wait(0);  // Wait indefinitely to ensure the fork will end because of a reset detection
          end
          begin : reset_thread
            wait(cfg.in_reset);
          end
        join_any
        disable fork;   // Terminates all descendants and sub-descendants of isolation_fork
        wait(!cfg.in_reset);
      end join
    end
  endtask

  // This function will be executed each time the reset monitor will detect a reset activity. As
  // the monitor will broadcast this activity on a UVM TLM port uvm_analysis_port which is connected
  // to this component via a UVM analysis import.
  virtual function void write_drv_reset(reset_state_e reset_st);
    if (reset_st == ResetAsserted) begin
      // TODO MVy: use under_reset or cfg.in_reset ?
      under_reset = 1;
    end else begin
      under_reset = 0;
    end
  endfunction : write_drv_reset

  // reset signals
  virtual task reset_signals();
    `uvm_fatal(`gfn, "this is implemented as pure virtual task - please extend")
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    `uvm_fatal(`gfn, "this is implemented as pure virtual task - please extend")
  endtask

endclass
