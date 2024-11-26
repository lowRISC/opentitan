// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class reset_base_seq extends dv_base_seq #(
  .REQ         (reset_item),
  .CFG_T       (reset_agent_cfg),
  .SEQUENCER_T (reset_sequencer)
);
// class reset_base_seq extends uvm_sequence #(reset_item);
//   `uvm_object_utils(reset_base_seq)

  // Standard SV/UVM methods
  extern function new (string name = "");
  extern virtual task pre_body();
  extern virtual task body();
  extern virtual task post_body();
endclass : reset_base_seq


function reset_base_seq::new(string name = "");
  super.new(name);
endfunction : new

task reset_base_seq::pre_body();
  `uvm_info(`gtn, {"Running sequence ", `gfn}, UVM_MEDIUM)
endtask : pre_body

task reset_base_seq::body();
  reset_item tr;
  tr = reset_item::type_id::create("tr");

  start_item(tr);

  if (!tr.randomize()) begin
    `uvm_fatal(`gfn, "Failed to randomize transaction !")
  end

  finish_item(tr);
endtask : body

task reset_base_seq::post_body();
  `uvm_info(`gtn, {"Completed sequence ", `gfn}, UVM_MEDIUM)
endtask : post_body
