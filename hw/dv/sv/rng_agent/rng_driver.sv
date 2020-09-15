// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rng_driver extends dv_base_driver #(.ITEM_T(rng_item),
                                          .CFG_T (rng_agent_cfg));
  `uvm_component_utils(rng_driver)

  rand bit[3:0]   entropy;

  // the base class provides the following handles for use:
  // rng_agent_cfg: cfg

  `uvm_component_new

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
  endtask

  // reset signals
  virtual task reset_signals();
  endtask

  // drive outputs based on inputs
  virtual task get_and_drive();
    forever begin
    @(posedge cfg.vif.enable iff cfg.vif.rst_n);
    do begin
      //randomize 1st entropy value so not always 0
      if (cfg.entropy_type == RAND) begin
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(entropy)
      end
      repeat (cfg.entropy_ok_delay_clks) @(posedge cfg.vif.clk);
      cfg.vif.entropy    = entropy;
      cfg.vif.entropy_ok = 1'b1;
      repeat (cfg.entropy_hold_clks) @(posedge cfg.vif.clk);
      //Increment here so initial INCR entropy is 0
      if (cfg.entropy_type == INCR) begin
        entropy += 1'b1;
      end
      @(posedge cfg.vif.clk);
      end
      while (cfg.vif.enable);
      cfg.vif.entropy_ok = 1'b0;
    end
  endtask

endclass
