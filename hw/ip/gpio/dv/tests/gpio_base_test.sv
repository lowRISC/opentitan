// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
class gpio_base_test extends cip_base_test #(
  .ENV_T(gpio_env),
  .CFG_T(gpio_env_cfg)
);
  `uvm_component_utils(gpio_base_test)
  
straps_vif straps_vif_inst; // Virtual interface
// Instance of the main sequence started in the base test
uvm_sequence main_seq;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  task reset_phase(uvm_phase phase);
    phase.raise_objection(this);
    // Initialize inputs
    straps_vif_inst.port_out.strap_en = 0;
    phase.drop_objection(this);
  endtask

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(straps_vif)::get(this, "*.*", "straps_vif", straps_vif_inst)) begin
      `uvm_fatal("gpio_base_test", "Virtual interface straps_vif_inst is not set")
    end
  endfunction : build_phase

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    main_seq = get_sequence_by_name(test_seq_s);
    if (main_seq == null) begin
      `uvm_fatal("gpio_base_test", "Could not get main_seq")
    end else begin
      main_seq.sqr_h = env.v_sequencer;
    end
  endtask
endclass : gpio_base_test
