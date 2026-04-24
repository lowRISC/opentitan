// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class key_sideload_item #(
    parameter type KEY_T = keymgr_pkg::hw_key_req_t
) extends uvm_sequence_item;
  localparam int KeyWidth = ($bits(KEY_T)-1)/keymgr_pkg::Shares;

  // random variables
  rand bit                valid;
  rand bit [KeyWidth-1:0] key0;
  rand bit [KeyWidth-1:0] key1;
  rand int unsigned       rsp_delay = 0;

  // A flag that can be set from outside by calling request_stop(). When this is true, the
  // wait_stop_requested() task will exit.
  local bit               m_stop_requested;

  constraint rsp_delay_constraint_c {rsp_delay inside {[0:9]};}

  `uvm_object_utils_begin(key_sideload_item#(KEY_T))
    `uvm_field_int(valid, UVM_DEFAULT)
    `uvm_field_int(key0,  UVM_DEFAULT)
    `uvm_field_int(key1,  UVM_DEFAULT)
    `uvm_field_int(rsp_delay,  UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name="");
    super.new(name);
  endfunction

  // Set a flag that will cause wait_stop_requested to exit
  function void request_stop();
    m_stop_requested = 1;
  endfunction

  // A task that runs until request_stop is called.
  //
  // This task is safe to kill.
  task wait_stop_requested();
    wait(m_stop_requested);
  endtask

endclass
